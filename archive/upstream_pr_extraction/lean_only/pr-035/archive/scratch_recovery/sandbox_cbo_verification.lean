import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-!
SANDBOX: Final Attempt.
Uses verified coe_toContinuousLinearMap' from Topology/Algebra/Module/FiniteDimension.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace CblinfunMatrix

open Matrix
open FiniteMatrix
open Module

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def ketBasis (n : Type*) [Fintype n] [DecidableEq n] :
    Basis n ℂ (FinKetSpace n) :=
  (EuclideanSpace.basisFun n ℂ).toBasis

theorem reproduce_failure (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOp (LinearMap.toMatrix (ketBasis ι) (ketBasis κ) T.toLinearMap) = T := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  unfold matrixOp
  -- coe_toContinuousLinearMap' strips the wrapper
  rw [LinearMap.coe_toContinuousLinearMap']
  -- Use deprecated but existing ofLp_toEuclideanLin_apply
  rw [Matrix.ofLp_toEuclideanLin_apply]
  -- Bridge: ofLp x i = (Basis.repr x) i
  have h_repr (x : FinKetSpace ι) : x.ofLp = (ketBasis ι).repr x := by
    ext j; rfl
  have h_repr_κ (x : FinKetSpace κ) : x.ofLp = (ketBasis κ).repr x := by
    ext j; rfl
  rw [h_repr, h_repr_κ]
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl


end CblinfunMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
