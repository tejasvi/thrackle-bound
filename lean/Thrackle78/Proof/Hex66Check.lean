import Thrackle78.Proof.Hex66Data

/-!
# The 6-6 certificate table is correct (kernel evaluation)
-/

namespace Thrackle78.Proof

/-- Every consistent assignment has a valid certificate. -/
theorem certOf66_ok : ∀ x0 x1 x2 x3 x4 : Option (Fin 5), validB66 [x0, x1, x2, x3, x4] = true →
    checkCert66 [x0, x1, x2, x3, x4] (certOf66 x0 x1 x2 x3 x4) = true := by
  decide +kernel

end Thrackle78.Proof
