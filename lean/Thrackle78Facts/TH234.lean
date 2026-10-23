import Thrackle78Core.BMOracle
import Thrackle78.Checker.OracleWalk
import Thrackle78.Theta

/-! `ThetaFacts.th234`: theta(2,3,4) (listing `lTH234` as run) is not combinatorially thrackleable (native oracle
search from the root, no filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem th234 : ¬ CombThr (mkE 8 lTH234) :=
  not_combThr_mkE_of_checkIO 8 lTH234 (by decide) [] (fun es => BM.bmOrcKR 8 es) (by native_decide)

end Thrackle78.Facts
