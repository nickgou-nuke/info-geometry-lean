import InfoGeometry.Canonical.PeirceBCFWKinematicBridge

namespace InfoGeometry.Canonical

/-! The Peirce channel carrier is equipped with its concrete Mathlib bilinear
form in `PeirceBCFWKinematicBridge`. Its null-locus readout is kept distinct
from the independent BCFW shift identities. -/

/-- A Peirce channel which lies on the quadratic null locus has zero value
under the concrete symmetric bilinear form. -/
theorem complexifiedChannel_isOnShell
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : splitQuadratic (embedRealSplit M) = 0) :
    peirceKinematicForm (complexifiedChannel M)
        (complexifiedChannel M) = 0 := by
  rw [complexifiedChannel_peirce_quadratic]
  exact_mod_cast hM

end InfoGeometry.Canonical
