import InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A genuine finite matrix-to-operator `StarAlgHom`

The source is the full finite matrix algebra `M₂(ℂ)` indexed by `Bool`; the
CAR operators are distinguished elements of it by the preceding bridge.  The
map below is the native continuous action on `EuclideanSpace ℂ Bool`.
This is a finite representation, not an assertion that the algebraic Cuntz
quotient is already represented on this carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCARStarAlgHom

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge
open InfoGeometry.Canonical.FiniteSingleModeCARHilbertTransport
open Matrix

abbrev MatrixOperator := FinKetSpace Bool →L[ℂ] FinKetSpace Bool

noncomputable def matrixOperatorAlgHom :
    Matrix Bool Bool ℂ →ₐ[ℂ] MatrixOperator :=
  { toFun := matrixOp
    map_one' := by
      simpa using (matrixOp_id (ι := Bool))
    map_mul' := by
      intro M N
      rw [ContinuousLinearMap.mul_def, matrixOp_comp]
    map_zero' := by
      simpa using (matrixOp_zero (κ := Bool) (ι := Bool))
    map_add' := by
      intro M N
      exact matrixOp_add M N
    commutes' := by
      intro r
      have hmap : (algebraMap ℂ (Matrix Bool Bool ℂ)) r =
          r • (1 : Matrix Bool Bool ℂ) := by
        simp [Algebra.smul_def]
      rw [hmap]
      ext v i
      cases i <;> simp [matrixOp_apply, Matrix.mulVec, dotProduct,
        Matrix.one_apply] }

noncomputable def matrixOperatorStarAlgHom :
    Matrix Bool Bool ℂ →⋆ₐ[ℂ] MatrixOperator :=
  { toAlgHom := matrixOperatorAlgHom
    map_star' := by
      intro M
      change matrixOp (star M) = star (matrixOp M)
      rw [ContinuousLinearMap.star_eq_adjoint, matrixOp_adjoint,
        Matrix.star_eq_conjTranspose] }

@[simp] theorem matrixOperatorStarAlgHom_apply (M : Matrix Bool Bool ℂ) :
    matrixOperatorStarAlgHom M = matrixOp M :=
  rfl

theorem matrixOperatorStarAlgHom_ann :
    matrixOperatorStarAlgHom annMatrix2 = annHilbert := by
  rw [matrixOperatorStarAlgHom_apply, annHilbert_eq_matrixOp]

theorem matrixOperatorStarAlgHom_cre :
    matrixOperatorStarAlgHom creMatrix2 = creHilbert := by
  rw [matrixOperatorStarAlgHom_apply, creHilbert_eq_matrixOp]

end InfoGeometry.Canonical.FiniteSingleModeCARStarAlgHom
