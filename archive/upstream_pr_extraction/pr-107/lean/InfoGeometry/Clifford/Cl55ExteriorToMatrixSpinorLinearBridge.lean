import InfoGeometry.Clifford.SplitClifford55ExteriorFiniteGraded
import InfoGeometry.Clifford.Cl55SpinorDimensionReadout

noncomputable section

namespace InfoGeometry.Clifford.Cl55ExteriorToMatrixSpinorLinearBridge

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55ExteriorDegrees
open InfoGeometry.Clifford.SpinorRep

local instance : FiniteDimensional ℝ (ExteriorAlgebra ℝ V5) :=
  Module.Basis.finiteDimensional_of_finite exteriorAlgebraFiniteBasis

theorem exteriorSpinor_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ V5) = 32 := by
  exact exteriorAlgebra_finrank

noncomputable def exteriorToMatrixSpinor :
    ExteriorAlgebra ℝ V5 ≃ₗ[ℝ] SpinorSpace 5 :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [exteriorSpinor_finrank, spinorSpace_five_finrank])

theorem exteriorToMatrixSpinor_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ V5) =
      Module.finrank ℝ (SpinorSpace 5) := by
  rw [exteriorSpinor_finrank, spinorSpace_five_finrank]

end InfoGeometry.Clifford.Cl55ExteriorToMatrixSpinorLinearBridge
