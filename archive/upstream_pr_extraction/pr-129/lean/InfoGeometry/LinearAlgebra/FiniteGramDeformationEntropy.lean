import InfoGeometry.LinearAlgebra.FiniteRelativeFrameEntropy

namespace InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy

open InfoGeometry.Cocycle
open InfoGeometry.LinearAlgebra.FiniteRelativeFrameEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite-dimensional Gram distortion associated with a real linear map. -/
def gramDistortion (J : Matrix n n ℝ) : Matrix n n ℝ :=
  J.transpose * J

/-- The scalar compression potential read from the Gram determinant. -/
noncomputable def gramCompressionPotential (J : Matrix n n ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (gramDistortion J).det

@[simp]
theorem det_gramDistortion (J : Matrix n n ℝ) :
    (gramDistortion J).det = J.det ^ 2 := by
  simp [gramDistortion, Matrix.det_mul, pow_two]

theorem det_gramDistortion_pos (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    0 < (gramDistortion J).det := by
  rw [det_gramDistortion]
  exact sq_pos_of_ne_zero hJ

theorem gramCompressionPotential_eq_neg_log_abs_det
    (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    gramCompressionPotential J = -Real.log |J.det| := by
  rw [gramCompressionPotential, det_gramDistortion, pow_two, Real.log_mul hJ hJ,
    Real.log_abs]
  ring

theorem gramCompressionPotential_eq_matrixLogdetBarrier
    (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    gramCompressionPotential J = matrixLogdetBarrier J := by
  rw [gramCompressionPotential_eq_neg_log_abs_det J hJ]
  rfl

theorem relativeFrameEntropy_eq_gramCompressionPotential
    (current reference : Frame (n := n)) :
    relativeFrameEntropy current reference =
      gramCompressionPotential (relativeJacobian current reference) := by
  symm
  unfold relativeFrameEntropy
  exact gramCompressionPotential_eq_matrixLogdetBarrier
    (relativeJacobian current reference)
    (relativeFrame current reference).det_ne_zero

end InfoGeometry.LinearAlgebra.FiniteGramDeformationEntropy
