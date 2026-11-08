import InfoGeometry.LinearAlgebra.FiniteJacobianLogDet
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

noncomputable section

namespace InfoGeometry.LinearAlgebra.FiniteRelativeFrameEntropy

open InfoGeometry.Cocycle

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Finite invertible real frames. -/
abbrev Frame :=
  Matrix.GeneralLinearGroup n ℝ

/-- Current-over-reference relative frame deformation. -/
def relativeFrame
    (current reference : Frame (n := n)) :
    Frame (n := n) :=
  current * reference⁻¹

/-- Matrix underlying the current-over-reference relative frame. -/
def relativeJacobian
    (current reference : Frame (n := n)) :
    Matrix n n ℝ :=
  relativeFrame current reference

/-- Negative logarithmic absolute-determinant entropy of a relative frame. -/
def relativeFrameEntropy
    (current reference : Frame (n := n)) : ℝ :=
  matrixLogdetBarrier (relativeJacobian current reference)

@[simp]
theorem relativeFrame_self
    (B : Frame (n := n)) :
    relativeFrame B B = 1 := by
  simp [relativeFrame]

@[simp]
theorem relativeJacobian_self
    (B : Frame (n := n)) :
    relativeJacobian B B = 1 := by
  simp [relativeJacobian]

@[simp]
theorem relativeFrameEntropy_self
    (B : Frame (n := n)) :
    relativeFrameEntropy B B = 0 := by
  simp [relativeFrameEntropy]

/-- Relative frames satisfy the multiplicative three-frame cocycle law. -/
theorem relativeFrame_cocycle
    (B₂ B₁ B₀ : Frame (n := n)) :
    relativeFrame B₂ B₀ =
      relativeFrame B₂ B₁ * relativeFrame B₁ B₀ := by
  simp [relativeFrame, mul_assoc]

/-- The matrix-valued relative Jacobians satisfy the same cocycle law. -/
theorem relativeJacobian_cocycle
    (B₂ B₁ B₀ : Frame (n := n)) :
    relativeJacobian B₂ B₀ =
      relativeJacobian B₂ B₁ * relativeJacobian B₁ B₀ := by
  change (relativeFrame B₂ B₀ : Matrix n n ℝ) =
    (relativeFrame B₂ B₁ : Matrix n n ℝ) *
      (relativeFrame B₁ B₀ : Matrix n n ℝ)
  rw [relativeFrame_cocycle]
  rfl

/-- Relative-frame entropy is additive along composable finite frames. -/
theorem relativeFrameEntropy_cocycle
    (B₂ B₁ B₀ : Frame (n := n)) :
    relativeFrameEntropy B₂ B₀ =
      relativeFrameEntropy B₂ B₁ +
        relativeFrameEntropy B₁ B₀ := by
  unfold relativeFrameEntropy
  rw [relativeJacobian_cocycle]
  exact matrixLogdetBarrier_mul
    (relativeJacobian B₂ B₁)
    (relativeJacobian B₁ B₀)
    (Matrix.GeneralLinearGroup.det_ne_zero (relativeFrame B₂ B₁))
    (Matrix.GeneralLinearGroup.det_ne_zero (relativeFrame B₁ B₀))

/-- Reversing the ordered frame pair inverts the relative deformation. -/
theorem relativeFrame_reverse
    (current reference : Frame (n := n)) :
    relativeFrame reference current =
      (relativeFrame current reference)⁻¹ := by
  simp [relativeFrame]

/-- Reversing the ordered frame pair negates finite deformation entropy. -/
theorem relativeFrameEntropy_reverse
    (current reference : Frame (n := n)) :
    relativeFrameEntropy reference current =
      -relativeFrameEntropy current reference := by
  have h :=
    relativeFrameEntropy_cocycle current reference current
  rw [relativeFrameEntropy_self] at h
  linarith

end InfoGeometry.LinearAlgebra.FiniteRelativeFrameEntropy
