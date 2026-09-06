import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open Matrix
open Module
open FiniteDimensional

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def ketBasis (n : Type*) [Fintype n] [DecidableEq n] :
    Basis n ℂ (EuclideanSpace ℂ n) :=
  (EuclideanSpace.basisFun n ℂ).toBasis

def matrixOfOp (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    Matrix κ ι ℂ :=
  LinearMap.toMatrix (ketBasis ι) (ketBasis κ) T.toLinearMap

def matrixOp (M : Matrix κ ι ℂ) : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin (ketBasis ι) (ketBasis κ) M)

theorem matrixOfOp_matrixOp (M : Matrix κ ι ℂ) :
    matrixOfOp (matrixOp M) = M := by
  unfold matrixOfOp matrixOp
  simp [LinearMap.toMatrix_toLin]

theorem matrixOp_matrixOfOp (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    matrixOp (matrixOfOp T) = T := by
  apply ContinuousLinearMap.coe_injective
  unfold matrixOp matrixOfOp
  simp [Matrix.toLin_toMatrix]

theorem matrixOfOp_adjoint (T : (EuclideanSpace ℂ ι) →L[ℂ] (EuclideanSpace ℂ κ)) :
    matrixOfOp (ContinuousLinearMap.adjoint T) = (matrixOfOp T)ᴴ := by
  unfold matrixOfOp ketBasis
  rw [← LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun ι ℂ) (EuclideanSpace.basisFun κ ℂ)]
  congr 1

