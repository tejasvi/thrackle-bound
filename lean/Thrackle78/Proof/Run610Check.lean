import Thrackle78.Proof.Run610C0
import Thrackle78.Proof.Run610C1
import Thrackle78.Proof.Run610C2
import Thrackle78.Proof.Run610C3
import Thrackle78.Proof.Run610C4
import Thrackle78.Proof.Run610C5
import Thrackle78.Proof.Run610C6
import Thrackle78.Proof.Run610C7
import Thrackle78.Proof.Run610C8
import Thrackle78.Proof.Run610C9
import Thrackle78.Proof.Run610C10

/-!
# The run-lemma certificate table is correct (kernel evaluation, in eleven slices)
-/

namespace Thrackle78.Proof

/-- Every valid pattern that a facial walk can have has a valid certificate. -/
theorem certOf610_ok : ∀ x5 x6 x7 x8 x9 : Fin 11, validB610 [x5.val, x6.val, x7.val, x8.val, x9.val] = true →
    violB [x5.val, x6.val, x7.val, x8.val, x9.val] = false →
    checkCert610 [x5.val, x6.val, x7.val, x8.val, x9.val] (certOf610 x5 x6 x7 x8 x9) = true := by
  intro x5
  fin_cases x5
  · exact certOf610_ok_0
  · exact certOf610_ok_1
  · exact certOf610_ok_2
  · exact certOf610_ok_3
  · exact certOf610_ok_4
  · exact certOf610_ok_5
  · exact certOf610_ok_6
  · exact certOf610_ok_7
  · exact certOf610_ok_8
  · exact certOf610_ok_9
  · exact certOf610_ok_10

end Thrackle78.Proof
