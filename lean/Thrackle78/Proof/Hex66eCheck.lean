import Thrackle78.Proof.Hex66eData

/-!
# The 6-6 edge-overlap certificate table is correct (kernel evaluation)
-/

namespace Thrackle78.Proof

/-- Every consistent assignment has a valid certificate. -/
theorem certOf66e_ok : ∀ x0 x1 x2 x3 : Option (Fin 4), validB66e [x0, x1, x2, x3] = true →
    checkCert66e [x0, x1, x2, x3] (certOf66e x0 x1 x2 x3) = true := by
  decide +kernel

end Thrackle78.Proof
