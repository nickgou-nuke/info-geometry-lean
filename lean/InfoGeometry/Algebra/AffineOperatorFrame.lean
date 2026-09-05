import Mathlib

/-!
# Affine changes of a three-component operator frame

The coefficients are real and central; the operators need not commute.
An affine frame is not a Lie-algebra automorphism. Its exact inverse removes
its scalar shift before applying the inverse coefficient matrix.

The old-coordinate pullback metric is M.transpose * M. The metric for the
original Casimir written in the new centered coordinates is E.transpose * E,
where E = M inverse. These two metric roles are not interchanged.
-/

noncomputable section

namespace InfoGeometry.Algebra.AffineOperatorFrame

open scoped BigOperators

abbrev FrameMatrix := Matrix (Fin 3) (Fin 3) ℝ

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- A coefficient matrix acts on an actual module of operator triples. -/
def matrixFrame (M : FrameMatrix) : (Fin 3 → A) →ₗ[ℝ] (Fin 3 → A) where
  toFun X i := ∑ j, M i j • X j
  map_add' X Y := by
    funext i
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' r X := by
    funext i
    simp [Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem matrixFrame_apply (M : FrameMatrix) (X : Fin 3 → A) (i : Fin 3) :
    matrixFrame M X i = ∑ j, M i j • X j := rfl

/-- Matrix composition is the actual composition of these linear maps. -/
theorem matrixFrame_mul (M N : FrameMatrix) (X : Fin 3 → A) :
    matrixFrame (M * N) X = matrixFrame M (matrixFrame N X) := by
  funext i
  simp only [matrixFrame_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

@[simp] theorem matrixFrame_one (X : Fin 3 → A) :
    matrixFrame (1 : FrameMatrix) X = X := by
  funext i
  simp [matrixFrame, Matrix.one_apply]

/-- Scalar identity offsets in the three operator components. -/
def centralOffset (b : Fin 3 → ℝ) : Fin 3 → A := fun i => b i • (1 : A)

/-- An affine operator-frame change, not an algebra homomorphism. -/
def affineFrame (M : FrameMatrix) (b : Fin 3 → ℝ) (X : Fin 3 → A) : Fin 3 → A :=
  matrixFrame M X + centralOffset b

@[simp] theorem affineFrame_centered (M : FrameMatrix) (b : Fin 3 → ℝ)
    (X : Fin 3 → A) : affineFrame M b X - centralOffset b = matrixFrame M X := by
  simp [affineFrame]

/-- A genuine inverse matrix suffices; no further squeeze is required. -/
theorem inverse_affineFrame (M : FrameMatrixˣ) (b : Fin 3 → ℝ) (X : Fin 3 → A) :
    matrixFrame (↑(M⁻¹) : FrameMatrix)
      (affineFrame (↑M) b X - centralOffset b) = X := by
  rw [affineFrame_centered, ← matrixFrame_mul]
  simp

/-- Reconstructing from centered inverse coordinates is two-sided. -/
theorem affineFrame_inverse (M : FrameMatrixˣ) (b : Fin 3 → ℝ) (Y : Fin 3 → A) :
    affineFrame (↑M) b (matrixFrame (↑(M⁻¹) : FrameMatrix) (Y - centralOffset b)) = Y := by
  rw [affineFrame, ← matrixFrame_mul]
  simp

/-- Central offsets do not change a raw operator commutator. -/
theorem central_shift_bracket (X Y : A) (a b : ℝ) :
    ⁅X + a • (1 : A), Y + b • (1 : A)⁆ = ⁅X, Y⁆ := by
  simp only [Ring.lie_def, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul]
  module

/-- The transformed bracket with all original structure data retained. -/
theorem affineFrame_bracket (M : FrameMatrix) (b : Fin 3 → ℝ)
    (X : Fin 3 → A) (i j : Fin 3) :
    ⁅affineFrame M b X i, affineFrame M b X j⁆ =
      ∑ k, ∑ l, (M i k * M j l) • ⁅X k, X l⁆ := by
  change ⁅matrixFrame M X i + b i • (1 : A),
      matrixFrame M X j + b j • (1 : A)⁆ = _
  rw [central_shift_bracket]
  simp only [matrixFrame_apply, Fin.sum_univ_three, add_lie, lie_add,
    smul_lie, lie_smul, smul_smul]

/-- Ordered operator quadratic form. Symmetry is not used to commute operators. -/
def operatorQuadratic (G : FrameMatrix) (X : Fin 3 → A) : A :=
  ∑ j, ∑ k, G j k • (X j * X k)

def sumSquares (X : Fin 3 → A) : A := ∑ i, X i * X i

/-- Pulling the Euclidean sum of squares back uses M.transpose * M. -/
theorem sumSquares_matrixFrame (M : FrameMatrix) (X : Fin 3 → A) :
    sumSquares (matrixFrame M X) = operatorQuadratic (M.transpose * M) X := by
  simp only [sumSquares, operatorQuadratic, matrixFrame_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_three, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_smul, add_smul]
  module

/-- Exact affine expansion, including the linear and constant terms. -/
theorem sumSquares_affineFrame (M : FrameMatrix) (b : Fin 3 → ℝ)
    (X : Fin 3 → A) :
    sumSquares (affineFrame M b X) =
      operatorQuadratic (M.transpose * M) X +
        (2 : ℝ) • (∑ i, b i • matrixFrame M X i) +
        (∑ i, b i * b i) • (1 : A) := by
  rw [← sumSquares_matrixFrame]
  simp only [sumSquares, affineFrame, centralOffset, Pi.add_apply,
    Fin.sum_univ_three, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, smul_add, add_smul]
  module

/-- The centered new-coordinate Casimir metric is E.transpose * E. -/
theorem inverse_metric_quadratic (M : FrameMatrixˣ) (b : Fin 3 → ℝ)
    (X : Fin 3 → A) :
    operatorQuadratic
      ((↑(M⁻¹) : FrameMatrix).transpose * (↑(M⁻¹) : FrameMatrix))
      (affineFrame (↑M) b X - centralOffset b) = sumSquares X := by
  rw [← sumSquares_matrixFrame, inverse_affineFrame]

/-- The correct inverse-frame orthonormalization identity. -/
theorem inverse_frame_metric (M : FrameMatrixˣ) :
    (↑(M⁻¹) : FrameMatrix) * ((↑M : FrameMatrix) * (↑M : FrameMatrix).transpose) *
      (↑(M⁻¹) : FrameMatrix).transpose = 1 := by
  calc
    _ = ((↑(M⁻¹) : FrameMatrix) * (↑M : FrameMatrix)) *
        ((↑M : FrameMatrix).transpose * (↑(M⁻¹) : FrameMatrix).transpose) := by
          noncomm_ring
    _ = 1 := by rw [← Matrix.transpose_mul]; simp

/-- An extra coefficient deformation after inversion acts on the recovered
frame; it is not removed by the previous inverse. -/
theorem extra_deformation_after_inverse (B : FrameMatrix) (M : FrameMatrixˣ)
    (b : Fin 3 → ℝ) (X : Fin 3 → A) :
    matrixFrame B (matrixFrame (↑(M⁻¹) : FrameMatrix)
      (affineFrame (↑M) b X - centralOffset b)) = matrixFrame B X := by
  rw [inverse_affineFrame]

end InfoGeometry.Algebra.AffineOperatorFrame
