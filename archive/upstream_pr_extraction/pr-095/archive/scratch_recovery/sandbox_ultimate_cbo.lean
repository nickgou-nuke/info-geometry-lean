import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-!
# ULTIMATE SANDBOX: CblinfunMatrix
Goal: 100% verified kernel closure for the operator-matrix bridge.
This content will be used to OVERWRITE the core file only when GREEN.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace CblinfunMatrix

open Matrix
open FiniteMatrix
open Module

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

@[simp]
theorem matrixOfOp_apply (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) (r : κ) (c : ι) :
    matrixOfOp T r c = (T (ketPi c)) r := by
  simp [matrixOfOp, LinearMap.toMatrix_apply, ketBasis, ketPi]

/-- `matrixOfOp` is left inverse to `matrixOp`. -/
@[simp]
theorem matrixOfOp_matrixOp (M : Matrix κ ι ℂ) :
    matrixOfOp (matrixOp M) = M := by
  unfold matrixOfOp matrixOp
  simp [ketBasis, Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- `matrixOp` is right inverse to `matrixOfOp`. -/
@[simp]
theorem matrixOp_matrixOfOp (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOp (matrixOfOp T) = T := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  unfold matrixOp matrixOfOp
  rw [LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.ofLp_toEuclideanLin_apply]
  have h_repr (x : FinKetSpace ι) : x.ofLp = (ketBasis ι).repr x := by
    ext j; rfl
  have h_repr_κ (x : FinKetSpace κ) : x.ofLp = (ketBasis κ).repr x := by
    ext j; rfl
  rw [h_repr, h_repr_κ]
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl

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

/-- Conjugate transpose is the adjoint for the finite coordinate operator. -/
theorem matrixOp_conjTranspose_eq_adjoint (M : Matrix κ ι ℂ) :
    matrixOp Mᴴ = ContinuousLinearMap.adjoint (matrixOp M) := by
  unfold matrixOp
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

@[simp]
theorem matrixOfOp_adjoint (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (ContinuousLinearMap.adjoint T) = (matrixOfOp T)ᴴ := by
  apply matrixOp_injective
  rw [matrixOp_matrixOfOp, matrixOp_conjTranspose_eq_adjoint, matrixOp_matrixOfOp]


end CblinfunMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
