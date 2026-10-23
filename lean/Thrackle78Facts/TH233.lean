import Thrackle78Core.BMOracle
import Thrackle78.Checker.OracleWalk
import Thrackle78.Theta

/-! `ThetaFacts.th233`: theta(2,3,3) (listing `lTH233` as run) is not combinatorially thrackleable (native oracle
search from the root, no filters). -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem th233 : ¬ CombThr (mkE 7 lTH233) :=
  not_combThr_mkE_of_checkIO 7 lTH233 (by decide) [] (fun es => BM.bmOrcKR 7 es) (by native_decide)

end Thrackle78.Facts
