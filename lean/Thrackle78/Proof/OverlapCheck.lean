import Thrackle78.Proof.OverlapData

/-!
# The certificate table is correct (kernel evaluation)
-/

namespace Thrackle78.Proof

/-- Every consistent assignment has a valid certificate. -/
theorem certOf_ok : ∀ x0 x1 x2 x3 : Option (Fin 6), validB [x0, x1, x2, x3] = true →
    checkCert [x0, x1, x2, x3] (certOf x0 x1 x2 x3) = true := by
  decide +kernel

end Thrackle78.Proof
