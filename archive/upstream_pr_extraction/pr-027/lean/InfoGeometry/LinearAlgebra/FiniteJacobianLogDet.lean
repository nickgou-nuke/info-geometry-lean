import InfoGeometry.Cocycle.LogarithmicOrderParameter

noncomputable section

namespace InfoGeometry.LinearAlgebra.FiniteJacobianLogDet

open InfoGeometry.Cocycle

variable {Map n : Type*}
variable [Fintype n] [DecidableEq n]

/-- A finite real matrix-valued Jacobian family. -/
structure MatrixJacobianFamily (Map n : Type*)
    [Fintype n] [DecidableEq n] where
  jacobian : Map → Matrix n n ℝ

namespace MatrixJacobianFamily

/-- Absolute determinant volume multiplier of a finite Jacobian. -/
def volumeMultiplier
    (J : MatrixJacobianFamily Map n)
    (φ : Map) : ℝ :=
  |(J.jacobian φ).det|

/-- Logarithmic absolute determinant of a finite Jacobian. -/
def logAbsDet
    (J : MatrixJacobianFamily Map n)
    (φ : Map) : ℝ :=
  Real.log (J.volumeMultiplier φ)

/-- Negative log-determinant deformation potential. -/
def compressionPotential
    (J : MatrixJacobianFamily Map n)
    (φ : Map) : ℝ :=
  -J.logAbsDet φ

@[simp]
theorem volumeMultiplier_eq_abs_det
    (J : MatrixJacobianFamily Map n)
    (φ : Map) :
    J.volumeMultiplier φ = |(J.jacobian φ).det| :=
  rfl

@[simp]
theorem logAbsDet_eq_log_abs_det
    (J : MatrixJacobianFamily Map n)
    (φ : Map) :
    J.logAbsDet φ = Real.log |(J.jacobian φ).det| :=
  rfl

@[simp]
theorem compressionPotential_eq_matrixLogdetBarrier
    (J : MatrixJacobianFamily Map n)
    (φ : Map) :
    J.compressionPotential φ =
      matrixLogdetBarrier (J.jacobian φ) :=
  rfl

/-- Pointwise product of two finite matrix-Jacobian families. -/
def mul
    (J₁ J₂ : MatrixJacobianFamily Map n) :
    MatrixJacobianFamily Map n where
  jacobian φ := J₁.jacobian φ * J₂.jacobian φ

@[simp]
theorem mul_jacobian
    (J₁ J₂ : MatrixJacobianFamily Map n)
    (φ : Map) :
    (J₁.mul J₂).jacobian φ =
      J₁.jacobian φ * J₂.jacobian φ :=
  rfl

/--
Composition of pointwise nonsingular finite Jacobians makes the compression
potential additive.
-/
theorem compressionPotential_mul
    (J₁ J₂ : MatrixJacobianFamily Map n)
    (φ : Map)
    (h₁ : (J₁.jacobian φ).det ≠ 0)
    (h₂ : (J₂.jacobian φ).det ≠ 0) :
    (J₁.mul J₂).compressionPotential φ =
      J₁.compressionPotential φ + J₂.compressionPotential φ := by
  change matrixLogdetBarrier (J₁.jacobian φ * J₂.jacobian φ) =
    matrixLogdetBarrier (J₁.jacobian φ) +
      matrixLogdetBarrier (J₂.jacobian φ)
  exact matrixLogdetBarrier_mul
    (J₁.jacobian φ) (J₂.jacobian φ) h₁ h₂

/-- A volume-preserving finite Jacobian has zero compression potential. -/
theorem compressionPotential_eq_zero_of_abs_det_eq_one
    (J : MatrixJacobianFamily Map n)
    (φ : Map)
    (hJ : |(J.jacobian φ).det| = 1) :
    J.compressionPotential φ = 0 := by
  change matrixLogdetBarrier (J.jacobian φ) = 0
  exact matrixLogdetBarrier_eq_zero_of_abs_det_eq_one
    (J.jacobian φ) hJ

/--
A nonsingular volume-compressing finite Jacobian has nonnegative compression
potential.
-/
theorem compressionPotential_nonneg_of_abs_det_le_one
    (J : MatrixJacobianFamily Map n)
    (φ : Map)
    (hJ₀ : (J.jacobian φ).det ≠ 0)
    (hJ₁ : |(J.jacobian φ).det| ≤ 1) :
    0 ≤ J.compressionPotential φ := by
  change 0 ≤ matrixLogdetBarrier (J.jacobian φ)
  exact matrixLogdetBarrier_nonneg_of_abs_det_le_one
    (J.jacobian φ) hJ₀ hJ₁

/--
A volume-expanding finite Jacobian has nonpositive compression potential.
-/
theorem compressionPotential_nonpos_of_one_le_abs_det
    (J : MatrixJacobianFamily Map n)
    (φ : Map)
    (hJ : 1 ≤ |(J.jacobian φ).det|) :
    J.compressionPotential φ ≤ 0 := by
  change matrixLogdetBarrier (J.jacobian φ) ≤ 0
  exact matrixLogdetBarrier_nonpos_of_one_le_abs_det
    (J.jacobian φ) hJ

end MatrixJacobianFamily

end InfoGeometry.LinearAlgebra.FiniteJacobianLogDet
