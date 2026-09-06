import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# SANDBOX: Clean CBO Substrate
Goal: 100% verified, sorry-free kernel closure.
Target: Operator-Matrix correspondence for FinKetSpace.
-/

noncomputable section

open Matrix
open Module
open FiniteDimensional

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The canonical coordinate basis for the finite ket space. -/
def ketBasis (n : Type*) [Fintype n] [DecidableEq n] :
    Basis n ℂ (EuclideanSpace ℂ n) :=
  (EuclideanSpace.basisFun n ℂ).toBasis

/-- Matrix of a bounded operator between finite ket spaces. -/
def matrixOfOp (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    Matrix κ ι ℂ :=
  LinearMap.toMatrix (ketBasis ι) (ketBasis κ) T.toLinearMap

/-- Operator from a matrix. -/
def matrixOp (M : Matrix κ ι ℂ) : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin (ketBasis ι) (ketBasis κ) M)

/-- Proof: matrixOfOp is left inverse to matrixOp. -/
theorem matrixOfOp_matrixOp (M : Matrix κ ι ℂ) :
    matrixOfOp (matrixOp M) = M := by
  unfold matrixOfOp matrixOp
  rw [LinearMap.coe_toContinuousLinearMap]
  rw [LinearMap.toMatrix_toLin]

/-- Proof: matrixOp is right inverse to matrixOfOp. -/
theorem matrixOp_matrixOfOp (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    matrixOp (matrixOfOp T) = T := by
  apply ContinuousLinearMap.coe_injective
  unfold matrixOp matrixOfOp
  rw [LinearMap.coe_toContinuousLinearMap]
  rw [LinearMap.toLin_toMatrix]

/-- Proof: matrixOfOp preserves adjoints. -/
theorem matrixOfOp_adjoint (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    matrixOfOp (ContinuousLinearMap.adjoint T) = (matrixOfOp T)ᴴ := by
  unfold matrixOfOp
  -- Goal: toMatrix (adjoint T).toLinearMap = (toMatrix T.toLinearMap)ᴴ
  -- ketBasis n is (basisFun n).toBasis
  have hB_ι : (ketBasis ι) = (EuclideanSpace.basisFun ι ℂ).toBasis := rfl
  have hB_κ : (ketBasis κ) = (EuclideanSpace.basisFun κ ℂ).toBasis := rfl
  rw [hB_ι, hB_κ]
  -- Use LinearMap.toMatrix_adjoint (OrthonormalBasis v1) (OrthonormalBasis v2) f
  rw [← LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun ι ℂ) (EuclideanSpace.basisFun κ ℂ) T.toLinearMap]
  -- Now we need: toMatrix (LinearMap.adjoint T.toLinearMap) = toMatrix (ContinuousLinearMap.adjoint T).toLinearMap
  congr 1
  ext x y
  rw [LinearMap.adjoint_inner_right]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl
