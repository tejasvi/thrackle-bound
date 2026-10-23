import Thrackle78.Proof.Run3S0
import Thrackle78.Proof.Run3S1
import Thrackle78.Proof.Run3S2
import Thrackle78.Proof.Run3S3
import Thrackle78.Proof.Run3S4
import Thrackle78.Proof.Run3S5
import Thrackle78.Proof.Run3S6
import Thrackle78.Proof.Run3S7
import Thrackle78.Proof.Run3S8
import Thrackle78.Proof.Run3S9
import Thrackle78.Proof.Run3S10
import Thrackle78.Proof.Run3S11

/-!
# The certificate table of the run lemma for `4/3` is correct (kernel evaluation, in 144 slices)
-/

namespace Thrackle78.Proof

/-- The certificate of a pattern `x4 … x9`. -/
def certOf3 (x4 x5 x6 x7 x8 x9 : Fin 12) : ℕ × List ℕ × List ℕ :=
  match x4 with
  | 0 => certOf3_0 x5 x6 x7 x8 x9
  | 1 => certOf3_1 x5 x6 x7 x8 x9
  | 2 => certOf3_2 x5 x6 x7 x8 x9
  | 3 => certOf3_3 x5 x6 x7 x8 x9
  | 4 => certOf3_4 x5 x6 x7 x8 x9
  | 5 => certOf3_5 x5 x6 x7 x8 x9
  | 6 => certOf3_6 x5 x6 x7 x8 x9
  | 7 => certOf3_7 x5 x6 x7 x8 x9
  | 8 => certOf3_8 x5 x6 x7 x8 x9
  | 9 => certOf3_9 x5 x6 x7 x8 x9
  | 10 => certOf3_10 x5 x6 x7 x8 x9
  | 11 => certOf3_11 x5 x6 x7 x8 x9

/-- Every valid pattern that a facial walk can have has a valid certificate. -/
theorem certOf3_ok : ∀ x4 x5 x6 x7 x8 x9 : Fin 12,
    validB3 [x4.val, x5.val, x6.val, x7.val, x8.val, x9.val] = true →
    violB3 [x4.val, x5.val, x6.val, x7.val, x8.val, x9.val] = false →
    checkCert3 [x4.val, x5.val, x6.val, x7.val, x8.val, x9.val] (certOf3 x4 x5 x6 x7 x8 x9) = true := by
  intro x4
  fin_cases x4
  · exact certOf3_ok_0
  · exact certOf3_ok_1
  · exact certOf3_ok_2
  · exact certOf3_ok_3
  · exact certOf3_ok_4
  · exact certOf3_ok_5
  · exact certOf3_ok_6
  · exact certOf3_ok_7
  · exact certOf3_ok_8
  · exact certOf3_ok_9
  · exact certOf3_ok_10
  · exact certOf3_ok_11

end Thrackle78.Proof
