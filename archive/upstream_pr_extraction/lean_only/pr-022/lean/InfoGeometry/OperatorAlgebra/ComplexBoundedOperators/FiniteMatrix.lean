import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite matrix adapter for AFP `Cblinfun_Code`

AFP's `Cblinfun_Code` represents finite-dimensional bounded operators by
matrices.  This file exposes the corresponding Lean-native surface:

* finite coordinate spaces are functions `ι → ℂ`;
* kets are `Pi.single i 1`;
* a matrix acts by `Matrix.mulVec`, packaged as a continuous linear map.
* finite matrix adjoints are represented by `Matrix.conjTranspose`.

This is intentionally finite-dimensional.  It is not a replacement for the
general counting-measure `ell2Count` API.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace FiniteMatrix

open Matrix

variable {ι κ λ : Type*}

/-- Finite coordinate ket space used by the matrix code adapter. -/
abbrev FinKetSpace (ι : Type*) : Type :=
  ι → ℂ

/-- Coordinate ket basis vector. -/
def ketPi [DecidableEq ι] (i : ι) : FinKetSpace ι :=
  Pi.single i 1

@[simp]
theorem ketPi_apply_self [DecidableEq ι] (i : ι) :
    ketPi i i = 1 := by
  simp [ketPi]

theorem ketPi_apply_of_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) :
    ketPi i j = 0 := by
  simp [ketPi, Pi.single_eq_of_ne hij]

/-- Matrix action on finite coordinate functions as a bounded complex-linear map. -/
def matrixOp [Fintype ι] [Fintype κ] (M : Matrix κ ι ℂ) :
    FinKetSpace ι →L[ℂ] FinKetSpace κ :=
  ({
    toFun := fun v => M *ᵥ v
    map_add' := by
      intro v w
      exact Matrix.mulVec_add M v w
    map_smul' := by
      intro c v
      exact Matrix.mulVec_smul M v c
  } : FinKetSpace ι →ₗ[ℂ] FinKetSpace κ).toContinuousLinearMap

@[simp]
theorem matrixOp_apply [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℂ) (v : FinKetSpace ι) :
    matrixOp M v = M *ᵥ v :=
  rfl

/-- A matrix sends a coordinate ket to the corresponding column. -/
theorem matrixOp_apply_ket [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix κ ι ℂ) (i : ι) :
    matrixOp M (ketPi i) = M.col i := by
  simp [matrixOp, ketPi, Matrix.mulVec_single_one]

/-- Matrix operator composition corresponds to matrix multiplication. -/
theorem matrixOp_comp [Fintype ι] [Fintype κ] [Fintype λ]
    (M : Matrix λ κ ℂ) (N : Matrix κ ι ℂ) :
    (matrixOp M).comp (matrixOp N) = matrixOp (M * N) := by
  ext v x
  simp [matrixOp, Matrix.mulVec_mulVec]

/-- The identity matrix acts as the identity operator. -/
theorem matrixOp_id [Fintype ι] [DecidableEq ι] :
    matrixOp (1 : Matrix ι ι ℂ) =
      ContinuousLinearMap.id ℂ (FinKetSpace ι) := by
  ext v x
  simp [matrixOp, Matrix.one_mulVec]

/-- The zero matrix acts as the zero operator. -/
theorem matrixOp_zero [Fintype ι] [Fintype κ] :
    matrixOp (0 : Matrix κ ι ℂ) =
      (0 : FinKetSpace ι →L[ℂ] FinKetSpace κ) := by
  ext v x
  simp [matrixOp, Matrix.zero_mulVec]

/-- Matrix addition corresponds to operator addition. -/
theorem matrixOp_add [Fintype ι] [Fintype κ]
    (M N : Matrix κ ι ℂ) :
    matrixOp (M + N) = matrixOp M + matrixOp N := by
  ext v x
  simp [matrixOp, Matrix.add_mulVec]

/-! ## Finite matrix adjoint corridor from AFP `Extra_Jordan_Normal_Form` -/

@[simp]
theorem conjTranspose_apply_entry (M : Matrix κ ι ℂ) (i : ι) (j : κ) :
    Mᴴ i j = star (M j i) :=
  rfl

theorem matrixOp_conjTranspose_apply_ket [Fintype ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (j : κ) (i : ι) :
    matrixOp Mᴴ (ketPi j) i = star (M j i) := by
  simp [matrixOp, ketPi, Matrix.mulVec_single_one]

/--
Finite-dimensional adjoint identity in AFP dot-product form.

This is the Lean-native analogue of AFP's `cscalar_prod_adjoint`:
the conjugate transpose is the adjoint for the standard finite coordinate
pairing.
-/
theorem dotProduct_conjTranspose_mulVec [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℂ) (v : FinKetSpace ι) (u : FinKetSpace κ) :
    star v ⬝ᵥ (Mᴴ *ᵥ u) = star (M *ᵥ v) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_conjTranspose]
  simp

end FiniteMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
