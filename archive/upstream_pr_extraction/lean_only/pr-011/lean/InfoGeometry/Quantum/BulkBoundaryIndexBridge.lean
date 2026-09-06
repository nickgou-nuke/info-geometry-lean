import InfoGeometry.KK.KasparovCycle
import InfoGeometry.Quantum.BulkBoundary

namespace InfoGeometry.Quantum.BulkBoundary

open InfoGeometry.Krein

open InfoGeometry.KK
open InfoGeometry.Canonical.AnalyticalIndex

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]
variable [KreinSpace H] [KreinGradedModule H]

/--
Frontier materialization (candidate 4):
If a Kasparov cycle has a nonzero analytical index, then the grading dimensions must
be mismatched. This provides the exact input needed for the bulk-boundary correspondence.
-/
theorem auto_bulk_boundary_correspondence_concrete_from_seed_4
    (X : KasparovCycle A B H)
    (hNonzero : X.analyticalIndex ≠ 0) :
    Module.finrank ℝ (chiralKernelSlicePlus (X.F.toLinearMap) (KreinGradedModule.gradeCLM (H := H)).toLinearMap) ≠
    Module.finrank ℝ (chiralKernelSliceMinus (X.F.toLinearMap) (KreinGradedModule.gradeCLM (H := H)).toLinearMap) := by
  intro hEq
  apply hNonzero
  unfold KasparovCycle.analyticalIndex InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex
  simp [hEq]

end InfoGeometry.Quantum.BulkBoundary
