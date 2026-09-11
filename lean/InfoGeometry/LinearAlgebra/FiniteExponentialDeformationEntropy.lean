import InfoGeometry.Cocycle.MatrixDetExpTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.LinearAlgebra.FiniteJacobianLogDet

noncomputable section

namespace InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy

open InfoGeometry.Cocycle

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Constant-generator finite matrix-exponential deformation. -/
def exponentialDeformation
    (A : Matrix n n ℝ)
    (t : ℝ) :
    Matrix n n ℝ :=
  NormedSpace.exp (t • A)

/-- Negative log-absolute-determinant entropy of an exponential deformation. -/
def exponentialDeformationEntropy
    (A : Matrix n n ℝ)
    (t : ℝ) : ℝ :=
  matrixLogdetBarrier (exponentialDeformation A t)

/--
The finite entropy of `exp (tA)` is exactly `-t trace(A)`.
-/
theorem exponentialDeformationEntropy_eq
    (A : Matrix n n ℝ)
    (t : ℝ) :
    exponentialDeformationEntropy A t =
      -t * Matrix.trace A := by
  unfold exponentialDeformationEntropy exponentialDeformation
  rw [matrixLogdetBarrier, logdetBarrier,
    InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real]
  rw [Matrix.trace_smul]
  rw [← Real.exp_eq_exp_ℝ]
  simp only [abs_of_pos (Real.exp_pos _), Real.log_exp, smul_eq_mul]
  ring

@[simp]
theorem exponentialDeformationEntropy_zero
    (A : Matrix n n ℝ) :
    exponentialDeformationEntropy A 0 = 0 := by
  rw [exponentialDeformationEntropy_eq]
  ring

/-- Entropy is additive in the time parameter for a constant generator. -/
theorem exponentialDeformationEntropy_add
    (A : Matrix n n ℝ)
    (s t : ℝ) :
    exponentialDeformationEntropy A (s + t) =
      exponentialDeformationEntropy A s +
        exponentialDeformationEntropy A t := by
  rw [exponentialDeformationEntropy_eq,
    exponentialDeformationEntropy_eq,
    exponentialDeformationEntropy_eq]
  ring

/-- A trace-free generator produces a volume-preserving exponential flow. -/
theorem exponentialDeformationEntropy_eq_zero_of_trace_eq_zero
    (A : Matrix n n ℝ)
    (hA : Matrix.trace A = 0) :
    ∀ t : ℝ, exponentialDeformationEntropy A t = 0 := by
  intro t
  rw [exponentialDeformationEntropy_eq, hA]
  ring

/-- The entropy-production rate of a constant exponential generator. -/
theorem hasDerivAt_exponentialDeformationEntropy
    (A : Matrix n n ℝ)
    (t : ℝ) :
    HasDerivAt
      (exponentialDeformationEntropy A)
      (-Matrix.trace A)
      t := by
  have h :
      exponentialDeformationEntropy A =
        fun u : ℝ => -u * Matrix.trace A := by
    funext u
    exact exponentialDeformationEntropy_eq A u
  rw [h]
  simpa using (hasDerivAt_id t).neg.mul_const (Matrix.trace A)

end InfoGeometry.LinearAlgebra.FiniteExponentialDeformationEntropy
