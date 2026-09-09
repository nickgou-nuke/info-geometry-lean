import InfoGeometry.Analysis.DirichletForm
/-!
# InfoGeometry.Analysis.SharpAngleEstimate
The full sharp-angle theorem for elliptic divergence forms is not encoded by
the finite algebraic carrier in this repository.  This module therefore keeps
only a concrete zero-coefficient model and proves its elementary sectorial
readout.  No inverse square root, operator norm, supremum, or analytic estimate
is silently represented by a scalar placeholder.
-/
namespace InfoGeometry.Analysis
/-/ The zero coefficient field used by the finite model. -/
def zeroCoefficientMatrix : ComplexCoefficientMatrix 3 :=
  fun _ _ _ => 0
theorem zeroCoefficient_model_is_sectorial :
    IsSectorialUnitForm zeroCoefficientMatrix 0 := by
  exact unitForm_is_sectorial_zero zeroCoefficientMatrix
end InfoGeometry.Analysis
