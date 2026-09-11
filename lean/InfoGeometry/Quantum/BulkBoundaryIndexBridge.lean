import InfoGeometry.KK.KasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.BulkBoundary

namespace InfoGeometry.Quantum.BulkBoundary

open InfoGeometry.Krein

open InfoGeometry.KK

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]
variable [KreinSpace H] [KreinGradedModule H]

/--
Frontier materialization (candidate 4):
If a Kasparov cycle has a nonzero analytical index, then the operatorial
plus/minus chiral defect sectors must have different finite dimensions. This
provides the exact input needed for the bulk-boundary correspondence.
-/
theorem auto_bulk_boundary_correspondence_concrete_from_seed_4
    (X : KasparovCycle A B H)
    (hNonzero : X.analyticalIndex ≠ 0) :
    Module.finrank ℝ (KasparovCycle.chiralKernelSlicePlus X) ≠
    Module.finrank ℝ (KasparovCycle.chiralKernelSliceMinus X) := by
  intro hEq
  have hEqInt :
      (Module.finrank ℝ (KasparovCycle.chiralKernelSlicePlus X) : ℤ) =
        (Module.finrank ℝ (KasparovCycle.chiralKernelSliceMinus X) : ℤ) := by
    exact congrArg Int.ofNat hEq
  have hEqIntPrimitive :
      (Module.finrank ℝ (RealSplitKreinKasparovCycle.chiralKernelSlicePlus X) : ℤ) =
        (Module.finrank ℝ (RealSplitKreinKasparovCycle.chiralKernelSliceMinus X) : ℤ) := by
    simpa [KasparovCycle.chiralKernelSlicePlus, KasparovCycle.chiralKernelSliceMinus] using hEqInt
  apply hNonzero
  unfold KasparovCycle.analyticalIndex RealSplitKreinKasparovCycle.finiteAnalyticalIndex
  rw [RealSplitKreinKasparovCycle.analyticalIndex_eq_finrank_chiralKernelDifference (X := X)]
  rw [hEqIntPrimitive]
  simp

end InfoGeometry.Quantum.BulkBoundary
