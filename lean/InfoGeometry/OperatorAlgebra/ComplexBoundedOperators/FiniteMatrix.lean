import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite matrix adapter for AFP `Cblinfun_Code`

AFP's `Cblinfun_Code` represents finite-dimensional bounded operators by
matrices.  This file exposes the corresponding Lean-native surface:

* finite coordinate spaces are `EuclideanSpace ℂ ι`;
* kets are standard basis vectors;
* a matrix acts by `Matrix.mulVec`, packaged as a continuous linear map.
* finite matrix adjoints are represented by `Matrix.conjTranspose`.

This is intentionally finite-dimensional.  It is not a replacement for the
general counting-measure `ell2Count` API.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace FiniteMatrix

open Matrix

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

/-- Finite coordinate ket space used by the matrix code adapter. -/
abbrev FinKetSpace (ι : Type*) [Fintype ι] : Type _ :=
  EuclideanSpace ℂ ι

/-- Coordinate ket basis vector. -/
def ketPi [DecidableEq ι] (i : ι) : FinKetSpace ι :=
  EuclideanSpace.single i 1

@[simp]
theorem ketPi_apply_self [DecidableEq ι] (i : ι) :
    (ketPi i : ι → ℂ) i = 1 := by
  simp [ketPi, EuclideanSpace.single_apply]

theorem ketPi_apply_of_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) :
    (ketPi i : ι → ℂ) j = 0 := by
  simp [ketPi, EuclideanSpace.single_apply, hij]

/-- Matrix action on finite coordinate functions as a bounded complex-linear map. -/
def matrixOp [DecidableEq ι] (M : Matrix κ ι ℂ) :
    FinKetSpace ι →L[ℂ] FinKetSpace κ :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

@[simp]
theorem matrixOp_apply [DecidableEq ι] (M : Matrix κ ι ℂ) (v : FinKetSpace ι) :
    (matrixOp M v : κ → ℂ) = M *ᵥ (v : ι → ℂ) := by
  simpa [matrixOp] using Matrix.toEuclideanLin_apply M v

/-- A matrix sends a coordinate ket to the corresponding column. -/
theorem matrixOp_apply_ket [DecidableEq ι]
    (M : Matrix κ ι ℂ) (i : ι) :
    (matrixOp M (ketPi i) : κ → ℂ) = M.col i := by
  ext j
  simp [matrixOp_apply, ketPi, EuclideanSpace.single_apply, Matrix.mulVec_single_one]

/-- Matrix operator composition corresponds to matrix multiplication. -/
theorem matrixOp_comp [DecidableEq ι] [DecidableEq κ]
    (M : Matrix η κ ℂ) (N : Matrix κ ι ℂ) :
    (matrixOp M).comp (matrixOp N) = matrixOp (M * N) := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [matrixOp_apply, Matrix.mulVec_mulVec]

/-- The identity matrix acts as the identity operator. -/
theorem matrixOp_id [DecidableEq ι] :
    matrixOp (1 : Matrix ι ι ℂ) =
      ContinuousLinearMap.id ℂ (FinKetSpace ι) := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [matrixOp_apply, Matrix.one_mulVec]

/-- The zero matrix acts as the zero operator. -/
theorem matrixOp_zero [DecidableEq ι] :
    matrixOp (0 : Matrix κ ι ℂ) =
      (0 : FinKetSpace ι →L[ℂ] FinKetSpace κ) := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [matrixOp_apply, Matrix.zero_mulVec]

/-- Matrix addition corresponds to operator addition. -/
theorem matrixOp_add [DecidableEq ι] (M N : Matrix κ ι ℂ) :
    matrixOp (M + N) = matrixOp M + matrixOp N := by
  apply ContinuousLinearMap.ext
  intro v
  ext x
  simp [matrixOp_apply, Matrix.add_mulVec]

/-! ## Finite matrix adjoint corridor from AFP `Extra_Jordan_Normal_Form` -/

theorem matrixOp_conjTranspose_apply_ket [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (j : κ) (i : ι) :
    (matrixOp Mᴴ (ketPi j) : ι → ℂ) i = star (M j i) := by
  simp [matrixOp_apply, ketPi, EuclideanSpace.single_apply, Matrix.mulVec_single_one]

/--
Finite-dimensional adjoint identity in AFP dot-product form.

This is the Lean-native analogue of AFP's `cscalar_prod_adjoint`:
the conjugate transpose is the adjoint for the standard finite coordinate
pairing.
-/
theorem dotProduct_conjTranspose_mulVec
    (M : Matrix κ ι ℂ) (v : ι → ℂ) (u : κ → ℂ) :
    dotProduct (star v) (Mᴴ *ᵥ u) = dotProduct (star (M *ᵥ v)) u := by
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_conjTranspose]
  simp

end FiniteMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
