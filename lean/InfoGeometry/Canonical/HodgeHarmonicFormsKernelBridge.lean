import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Closed and Coclosed Forms are Harmonic (d ω = 0 ∧ d* ω = 0 → Δ ω = 0). -/
theorem coclosed_and_closed_implies_harmonic
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hclosed : d omega = 0) (hcoclosed : dstar omega = 0) :
    hodgeDeRhamLaplacian d dstar omega = 0 := by
  dsimp [hodgeDeRhamLaplacian]
  rw [hcoclosed, hclosed, LinearMap.map_zero, LinearMap.map_zero, add_zero]

/-- **Theorem**: Dirac-Kähler Zero Mode Annihilation (D ω = 0 → (d + d*) ω = 0). -/
theorem dirac_kahler_zero_mode
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hdirac : diracKahlerOp d dstar omega = 0) :
    d omega + dstar omega = 0 := by
  exact hdirac

end InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
