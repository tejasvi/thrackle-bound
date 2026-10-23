import Thrackle78Core.Reader
import Thrackle78.Checker.MkE

/-!
# Probe: the 4-cycle is not combinatorially thrackleable (kernel-only, end to end)

The certificate (7 records: six expansions and one `K₅` model of the complete augmented graph) was produced by the
untrusted search; the proof checks it with `decide +kernel`. A corrupted copy (one vertex id changed) is rejected.
-/

namespace Thrackle78.Checker

open Thrackle78Core

/-- The certificate for the listing `[(0,1),(1,2),(2,3),(3,0)]`. -/
def c4Cert : String :=
  "E\nE\nE\nE\nE\nE\nK 1 0 0 1 1 0 2 2 0 6 0 1 3 0 1 11 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0\n"

/-- The same certificate with the vertex `6` of branch set `2` replaced by `7`. -/
def c4CertBad : String :=
  "E\nE\nE\nE\nE\nE\nK 1 0 0 1 1 0 2 2 0 7 0 1 3 0 1 11 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0\n"

theorem c4_check : check 4 [(0, 1), (1, 2), (2, 3), (3, 0)].toArray (textReader c4Cert.toUTF8) = true := by
  decide +kernel

theorem c4_check_bad : check 4 [(0, 1), (1, 2), (2, 3), (3, 0)].toArray (textReader c4CertBad.toUTF8) = false := by
  decide +kernel

/-- `C4` (as the listing `[(0,1),(1,2),(2,3),(3,0)]`) is not combinatorially thrackleable. -/
theorem not_combThr_C4 : ¬ CombThr (mkE 4 [(0, 1), (1, 2), (2, 3), (3, 0)]) :=
  not_combThr_mkE_of_check 4 _ (by decide) _ c4_check

end Thrackle78.Checker
