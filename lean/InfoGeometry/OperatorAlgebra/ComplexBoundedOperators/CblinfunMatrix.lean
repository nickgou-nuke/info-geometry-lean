import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-!
# AFP CBO `Cblinfun_Matrix` adapters

AFP's `Cblinfun_Matrix` identifies finite-dimensional bounded operators with
matrices relative to a canonical finite basis.  In Lean, for finite coordinate
spaces, this is the native equivalence between:

* `Matrix κ ι ℂ`
* `FinKetSpace ι →L[ℂ] FinKetSpace κ`

This file uses Mathlib's native matrix-linear map equivalences to provide
a clean, verified substrate for the unified algebra.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace CblinfunMatrix

open Matrix
open FiniteMatrix
open Module
open FiniteDimensional

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq η]

/-- The canonical coordinate basis for the finite ket space. -/
def ketBasis (n : Type*) [Fintype n] [DecidableEq n] :
    Basis n ℂ (FinKetSpace n) :=
  (EuclideanSpace.basisFun n ℂ).toBasis

/-- Coordinate matrix of a bounded operator between finite ket spaces. -/
def matrixOfOp (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    Matrix κ ι ℂ :=
  LinearMap.toMatrix (ketBasis ι) (ketBasis κ) T.toLinearMap

/-- Operator from a matrix relative to the canonical coordinate basis. -/
def matrixOp (M : Matrix κ ι ℂ) : FinKetSpace ι →L[ℂ] FinKetSpace κ :=
  LinearMap.toContinuousLinearMap (Matrix.toLin (ketBasis ι) (ketBasis κ) M)

/-- `matrixOfOp` is left inverse to `matrixOp`. -/
@[simp]
theorem matrixOfOp_matrixOp (M : Matrix κ ι ℂ) :
    matrixOfOp (matrixOp M) = M := by
  unfold matrixOfOp matrixOp
  simp [LinearMap.toMatrix_toLin]

/-- `matrixOp` is right inverse to `matrixOfOp`. -/
@[simp]
theorem matrixOp_matrixOfOp (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOp (matrixOfOp T) = T := by
  apply ContinuousLinearMap.coe_injective
  unfold matrixOp matrixOfOp
  simp [Matrix.toLin_toMatrix]

theorem matrixOfOp_injective :
    Function.Injective
      (matrixOfOp (ι := ι) (κ := κ) : (FinKetSpace ι →L[ℂ] FinKetSpace κ) → Matrix κ ι ℂ) :=
  (LinearMap.toMatrix (ketBasis ι) (ketBasis κ)).injective.comp ContinuousLinearMap.coe_injective

theorem matrixOp_injective :
    Function.Injective (matrixOp (ι := ι) (κ := κ) : Matrix κ ι ℂ → FinKetSpace ι →L[ℂ] FinKetSpace κ) := by
  intro M N h
  rw [← matrixOfOp_matrixOp M, ← matrixOfOp_matrixOp N, h]

@[simp]
theorem matrixOfOp_zero :
    matrixOfOp (0 : FinKetSpace ι →L[ℂ] FinKetSpace κ) = 0 :=
  (LinearMap.toMatrix (ketBasis ι) (ketBasis κ)).map_zero

@[simp]
theorem matrixOfOp_add (S T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (S + T) = matrixOfOp S + matrixOfOp T :=
  (LinearMap.toMatrix (ketBasis ι) (ketBasis κ)).map_add S.toLinearMap T.toLinearMap

@[simp]
theorem matrixOfOp_id :
    matrixOfOp (ContinuousLinearMap.id ℂ (FinKetSpace ι)) = 1 :=
  LinearMap.toMatrix_id _

@[simp]
theorem matrixOfOp_comp (S : FinKetSpace κ →L[ℂ] FinKetSpace η)
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (S.comp T) = matrixOfOp S * matrixOfOp T :=
  LinearMap.toMatrix_comp (ketBasis ι) (ketBasis κ) (ketBasis η) S.toLinearMap T.toLinearMap

@[simp]
theorem matrixOfOp_adjoint (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (ContinuousLinearMap.adjoint T) = (matrixOfOp T)ᴴ := by
  unfold matrixOfOp ketBasis
  rw [← LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun ι ℂ) (EuclideanSpace.basisFun κ ℂ)]
  congr 1

end CblinfunMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
