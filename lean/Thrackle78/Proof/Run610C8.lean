import Thrackle78.Proof.Run610Data

/-! The run-lemma certificate table, slice `w₅ = 8` (kernel evaluation). -/

namespace Thrackle78.Proof

set_option maxHeartbeats 0 in
theorem certOf610_ok_8 : ∀ x6 x7 x8 x9 : Fin 11, validB610 [8, x6.val, x7.val, x8.val, x9.val] = true →
    violB [8, x6.val, x7.val, x8.val, x9.val] = false →
    checkCert610 [8, x6.val, x7.val, x8.val, x9.val] (certOf610 8 x6 x7 x8 x9) = true := by
  decide +kernel

end Thrackle78.Proof
