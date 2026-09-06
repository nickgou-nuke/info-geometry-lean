import proofs.ChiralPoincareSouriauBridge
import proofs.LightConeConf3DeRhamCooperad

/-!
# Light-cone quadric as determinant/null cone of `2×2` complex matrices

This file records the algebraic bridge behind the user's observation:

* complexified Minkowski vectors are Pauli-soldered into `2×2` complex matrices;
* the light-cone quadric is the determinant quadric `det X = 0`;
* a normalized rank-one matrix/idempotent is a tripotent (`P³=P`) and lies on
  the determinant-zero quadric;
* the claim that every nonzero null matrix is a scalar multiple of a normalized
  tripotent/rank-one partial-isometry is not asserted here.

So: yes, in the `D=4` spinor model, the light-cone quadric is the null cone of
`det` on `M₂(C)`, and the tripotent decomposition is a normalization of the
rank-one part of that cone, not literally every null vector without scaling.
-/

noncomputable section

namespace LightConeTripotentMatrixBridge

open Matrix
open ChiralPoincareSouriauBridge

/-- The determinant quadratic form on `2×2` complex matrices. -/
def detQuadric (X : M2C) : ℂ := X.det

/-- Matrix null cone for the determinant/light-cone quadric. -/
def MatrixLightCone (X : M2C) : Prop := detQuadric X = 0

/-- Nonisotropic/non-null matrix edge condition. -/
def MatrixNonIsotropic (X : M2C) : Prop := detQuadric X ≠ 0

/-- Algebraic tripotent condition in the associative matrix algebra. -/
def IsAssociativeTripotent (X : M2C) : Prop := X * X * X = X

/-- A basic rank-one projector/tripotent. -/
def E00 : M2C := !![(1 : ℂ), 0; 0, 0]

@[simp] theorem E00_det : detQuadric E00 = 0 := by
  simp [detQuadric, E00, Matrix.det_fin_two]

@[simp] theorem E00_lightCone : MatrixLightCone E00 := by
  unfold MatrixLightCone
  rw [E00_det]

@[simp] theorem E00_tripotent : IsAssociativeTripotent E00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E00, Matrix.mul_apply]

/-- A concrete rank-one matrix `u vᵀ`. -/
def rankOneMatrix (u v : Fin 2 → ℂ) : M2C :=
  fun i j => u i * v j

/-- Every concrete outer-product `u vᵀ` lies on the determinant-zero quadric. -/
theorem rankOneMatrix_det_zero (u v : Fin 2 → ℂ) :
    detQuadric (rankOneMatrix u v) = 0 := by
  simp [detQuadric, rankOneMatrix, Matrix.det_fin_two]
  ring

/-- Hence every outer-product representative is a null/light-cone matrix. -/
theorem rankOneMatrix_lightCone (u v : Fin 2 → ℂ) :
    MatrixLightCone (rankOneMatrix u v) := by
  unfold MatrixLightCone
  rw [rankOneMatrix_det_zero u v]

/-- Pauli soldering identifies the determinant quadric with the Minkowski
quadratic form. -/
theorem detQuadric_pauliMomentum (P : FourMomentum) :
    detQuadric (pauliMomentum P) = minkowskiSq P :=
  det_pauliMomentum P

/-- The Pauli-soldered matrix is null exactly when the Minkowski square vanishes. -/
theorem pauli_lightCone_iff_minkowski_null (P : FourMomentum) :
    MatrixLightCone (pauliMomentum P) ↔ minkowskiSq P = 0 := by
  unfold MatrixLightCone detQuadric
  rw [det_pauliMomentum]

/-- The Pauli-soldered edge is nonisotropic exactly when the Minkowski square is
nonzero. -/
theorem pauli_nonisotropic_iff_minkowski_nonzero (P : FourMomentum) :
    MatrixNonIsotropic (pauliMomentum P) ↔ minkowskiSq P ≠ 0 := by
  unfold MatrixNonIsotropic detQuadric
  rw [det_pauliMomentum]

end LightConeTripotentMatrixBridge

end noncomputable section
