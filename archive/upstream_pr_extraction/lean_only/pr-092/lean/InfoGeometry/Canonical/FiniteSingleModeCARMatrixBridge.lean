import InfoGeometry.Canonical.FiniteSingleModeCARHilbertTransport
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-!
# Explicit matrix realization of the transported finite CAR operators

The two one-mode operators are represented by the usual nilpotent `2 × 2`
matrices over `Bool`.  All identities below are finite matrix identities; no
infinite Fock or Cuntz representation is inferred from them.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.Algebra.FiniteSingleModeCAR
open InfoGeometry.Canonical.FiniteSingleModeCAROperatorAlgebra
open InfoGeometry.Canonical.FiniteSingleModeCARHilbertTransport
open Matrix

def annMatrix2 : Matrix Bool Bool ℂ :=
  fun i j => if i then 0 else if j then 1 else 0

def creMatrix2 : Matrix Bool Bool ℂ :=
  fun i j => if i then if j then 0 else 1 else 0

theorem annMatrix2_conjTranspose : annMatrix2ᴴ = creMatrix2 := by
  ext i j
  cases i <;> cases j <;> simp [annMatrix2, creMatrix2]

theorem creMatrix2_conjTranspose : creMatrix2ᴴ = annMatrix2 := by
  rw [← annMatrix2_conjTranspose]
  simp

theorem annMatrix2_CAR :
    annMatrix2 * creMatrix2 + creMatrix2 * annMatrix2 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [annMatrix2, creMatrix2, Matrix.mul_apply]

theorem annMatrix2_nilpotent : annMatrix2 * annMatrix2 = 0 := by
  ext i j
  cases i <;> cases j <;> simp [annMatrix2, Matrix.mul_apply]

theorem creMatrix2_nilpotent : creMatrix2 * creMatrix2 = 0 := by
  ext i j
  cases i <;> cases j <;> simp [creMatrix2, Matrix.mul_apply]

theorem annHilbert_eq_matrixOp :
    annHilbert = matrixOp annMatrix2 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  cases i <;>
    simp [annHilbert, annContinuousLinearMap_apply, coordinateEquiv,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply,
      annMatrix2, matrixOp_apply, Matrix.mulVec, dotProduct, ann]

theorem creHilbert_eq_matrixOp :
    creHilbert = matrixOp creMatrix2 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  cases i <;>
    simp [creHilbert, creContinuousLinearMap_apply, coordinateEquiv,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply,
      creMatrix2, matrixOp_apply, Matrix.mulVec, dotProduct, cre]

theorem matrixOp_CAR :
    (matrixOp annMatrix2).comp (matrixOp creMatrix2) +
        (matrixOp creMatrix2).comp (matrixOp annMatrix2) =
      ContinuousLinearMap.id ℂ (FinKetSpace Bool) := by
  rw [matrixOp_comp, matrixOp_comp, ← matrixOp_add, annMatrix2_CAR,
    matrixOp_id]

theorem matrixOp_ann_adjoint :
    ContinuousLinearMap.adjoint (matrixOp annMatrix2) =
      matrixOp creMatrix2 := by
  rw [← annHilbert_eq_matrixOp, annHilbert_adjoint, creHilbert_eq_matrixOp]

theorem matrixOp_adjoint (M : Matrix Bool Bool ℂ) :
    ContinuousLinearMap.adjoint (matrixOp M) = matrixOp Mᴴ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [matrixOp_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct]
  ring

end InfoGeometry.Canonical.FiniteSingleModeCARMatrixBridge
