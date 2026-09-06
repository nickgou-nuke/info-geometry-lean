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

/-- **Theorem**: A Dirac--Kähler zero mode has vanishing summed operator
    readout.  This is the direct algebraic unfolding of the chosen operator
    definition; it does not assert the converse or an analytic zero-mode
    classification. -/
theorem dirac_kahler_zero_mode
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hdirac : diracKahlerOp d dstar omega = 0) :
    d omega + dstar omega = 0 := by
  exact hdirac

/-- **Theorem**: Finite algebraic package for a closed and coclosed form.
    It records the implication to the chosen Hodge--de Rham Laplacian and the
    definitional Dirac--Kähler readout.  It does not assert an analytic Hodge
    decomposition, an index theorem, or a converse zero-mode classification. -/
theorem master_hodge_harmonic_forms_kernel_synthesis
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (omega : ExteriorAlgebra R V)
    (hclosed : d omega = 0) (hcoclosed : dstar omega = 0) :
    (hodgeDeRhamLaplacian d dstar omega = 0) ∧
    (diracKahlerOp d dstar omega = d omega + dstar omega) := ⟨
  coclosed_and_closed_implies_harmonic d dstar omega hclosed hcoclosed,
  rfl
⟩

end InfoGeometry.Canonical.HodgeHarmonicFormsKernelBridge
