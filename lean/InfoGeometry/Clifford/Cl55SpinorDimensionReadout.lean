import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite `Cl(5,5)` spinor carrier

The split Clifford algebra itself is not identified here with a matrix
algebra.  The existing tensor-spinor carrier at stage `5` is the explicit
real function space `Fin 32 → ℝ`; this file records only its kernel-checked
dimension, which is the correct finite datum for later readout constructions.
-/

namespace InfoGeometry.Clifford.SpinorRep

theorem spinorSpace_five_finrank :
    Module.finrank ℝ (SpinorSpace 5) = 32 := by
  simp [SpinorSpace, Module.finrank_fintype_fun_eq_card]

theorem spinorSpace_five_finiteDimensional :
    FiniteDimensional ℝ (SpinorSpace 5) := by
  infer_instance

end InfoGeometry.Clifford.SpinorRep
