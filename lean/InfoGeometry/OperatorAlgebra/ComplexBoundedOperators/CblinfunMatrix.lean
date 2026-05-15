import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# AFP CBO `Cblinfun_Matrix` adapters

AFP's `Cblinfun_Matrix` identifies finite-dimensional bounded operators with
matrices relative to a canonical finite basis.  In Lean, for finite coordinate
spaces, this is the native equivalence between:

* `Matrix κ ι ℂ`
* `FinKetSpace ι →L[ℂ] FinKetSpace κ`

The forward map is `FiniteMatrix.matrixOp`.  This file adds the reverse map
`matrixOfOp` and proves the inverse and operation laws.
-/

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace CblinfunMatrix

open Matrix
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

variable {ι κ η : Type*}

/-- Coordinate matrix of a bounded operator between finite ket spaces. -/
def matrixOfOp [Fintype ι] [DecidableEq ι]
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    Matrix κ ι ℂ :=
  fun r c => T (ketPi c) r

@[simp]
theorem matrixOfOp_apply [Fintype ι] [DecidableEq ι]
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) (r : κ) (c : ι) :
    matrixOfOp T r c = T (ketPi c) r :=
  rfl

/-- Finite coordinate vectors decompose into the ket basis. -/
theorem finiteKet_decompose [Fintype ι] [DecidableEq ι] (v : FinKetSpace ι) :
    (∑ i : ι, v i • ketPi i) = v := by
  ext j
  simp [ketPi]

/-- `matrixOfOp` is left inverse to `matrixOp`. -/
@[simp]
theorem matrixOfOp_matrixOp [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix κ ι ℂ) :
    matrixOfOp (matrixOp M) = M := by
  ext r c
  simp [matrixOfOp, matrixOp_apply_ket]

/-- `matrixOp` is right inverse to `matrixOfOp`. -/
@[simp]
theorem matrixOp_matrixOfOp [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOp (matrixOfOp T) = T := by
  ext v r
  calc
    matrixOp (matrixOfOp T) v r
        = (∑ i : ι, matrixOfOp T r i * v i) := by
            simp [matrixOp, Matrix.mulVec, Matrix.dotProduct]
    _ = (∑ i : ι, (v i • T (ketPi i)) r) := by
            simp [matrixOfOp, mul_comm]
    _ = T (∑ i : ι, v i • ketPi i) r := by
            simp [map_sum]
    _ = T v r := by
            rw [finiteKet_decompose]

theorem matrixOfOp_injective [Fintype ι] [DecidableEq ι] [Fintype κ] :
    Function.Injective
      (matrixOfOp (ι := ι) (κ := κ) : (FinKetSpace ι →L[ℂ] FinKetSpace κ) → Matrix κ ι ℂ) := by
  intro S T h
  rw [← matrixOp_matrixOfOp S, ← matrixOp_matrixOfOp T, h]

theorem matrixOp_injective [Fintype ι] [DecidableEq ι] [Fintype κ] :
    Function.Injective (matrixOp (ι := ι) (κ := κ) : Matrix κ ι ℂ → FinKetSpace ι →L[ℂ] FinKetSpace κ) := by
  intro M N h
  rw [← matrixOfOp_matrixOp M, ← matrixOfOp_matrixOp N, h]

theorem op_eq_of_matrixOfOp_eq [Fintype ι] [DecidableEq ι] [Fintype κ]
    {S T : FinKetSpace ι →L[ℂ] FinKetSpace κ}
    (h : matrixOfOp S = matrixOfOp T) :
    S = T :=
  matrixOfOp_injective h

theorem matrixOfOp_eq_of_op_eq [Fintype ι] [DecidableEq ι]
    {S T : FinKetSpace ι →L[ℂ] FinKetSpace κ}
    (h : S = T) :
    matrixOfOp S = matrixOfOp T := by
  rw [h]

@[simp]
theorem matrixOfOp_zero [Fintype ι] [DecidableEq ι] [Fintype κ] :
    matrixOfOp (0 : FinKetSpace ι →L[ℂ] FinKetSpace κ) = 0 := by
  ext r c
  simp [matrixOfOp]

@[simp]
theorem matrixOfOp_add [Fintype ι] [DecidableEq ι] [Fintype κ]
    (S T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (S + T) = matrixOfOp S + matrixOfOp T := by
  ext r c
  simp [matrixOfOp]

@[simp]
theorem matrixOfOp_neg [Fintype ι] [DecidableEq ι] [Fintype κ]
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (-T) = -matrixOfOp T := by
  ext r c
  simp [matrixOfOp]

@[simp]
theorem matrixOfOp_sub [Fintype ι] [DecidableEq ι] [Fintype κ]
    (S T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (S - T) = matrixOfOp S - matrixOfOp T := by
  ext r c
  simp [sub_eq_add_neg]

@[simp]
theorem matrixOfOp_smul [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a : ℂ) (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (a • T) = a • matrixOfOp T := by
  ext r c
  simp [matrixOfOp]

@[simp]
theorem matrixOfOp_id [Fintype ι] [DecidableEq ι] :
    matrixOfOp (ContinuousLinearMap.id ℂ (FinKetSpace ι)) = 1 := by
  ext r c
  simp [matrixOfOp, ketPi, Matrix.one_apply, Pi.single_apply]

@[simp]
theorem matrixOfOp_comp [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype η]
    (S : FinKetSpace κ →L[ℂ] FinKetSpace η)
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (S.comp T) = matrixOfOp S * matrixOfOp T := by
  apply matrixOp_injective (ι := ι) (κ := η)
  rw [matrixOp_matrixOfOp, matrixOp_comp, matrixOp_matrixOfOp, matrixOp_matrixOfOp]

@[simp]
theorem matrixOp_of_add [Fintype ι] [Fintype κ]
    (M N : Matrix κ ι ℂ) :
    matrixOp (M + N) = matrixOp M + matrixOp N :=
  FiniteMatrix.matrixOp_add M N

@[simp]
theorem matrixOp_of_zero [Fintype ι] [Fintype κ] :
    matrixOp (0 : Matrix κ ι ℂ) =
      (0 : FinKetSpace ι →L[ℂ] FinKetSpace κ) :=
  FiniteMatrix.matrixOp_zero

@[simp]
theorem matrixOp_of_id [Fintype ι] [DecidableEq ι] :
    matrixOp (1 : Matrix ι ι ℂ) =
      ContinuousLinearMap.id ℂ (FinKetSpace ι) :=
  FiniteMatrix.matrixOp_id

theorem matrixOp_of_mul [Fintype ι] [Fintype κ] [Fintype η]
    (M : Matrix η κ ℂ) (N : Matrix κ ι ℂ) :
    matrixOp (M * N) = (matrixOp M).comp (matrixOp N) := by
  rw [FiniteMatrix.matrixOp_comp]

/-- Coordinate inner product in dot-product form. -/
theorem finiteKet_inner_eq_dotProduct [Fintype ι]
    (x y : FinKetSpace ι) :
    ⟪x, y⟫_ℂ = dotProduct (star x) y := by
  simp [PiLp.inner_apply, Matrix.dotProduct]

/-- Conjugate transpose is the adjoint for the finite coordinate operator. -/
theorem matrixOp_conjTranspose_eq_adjoint [Fintype ι] [DecidableEq ι] [Fintype κ]
    (M : Matrix κ ι ℂ) :
    matrixOp Mᴴ = ContinuousLinearMap.adjoint (matrixOp M) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext
  intro i
  have hinner :
      ∀ v : FinKetSpace ι,
        ⟪v, matrixOp Mᴴ u⟫_ℂ = ⟪v, (ContinuousLinearMap.adjoint (matrixOp M)) u⟫_ℂ := by
    intro v
    rw [ContinuousLinearMap.adjoint_inner_right]
    simpa [matrixOp, finiteKet_inner_eq_dotProduct] using
      (FiniteMatrix.dotProduct_conjTranspose_mulVec M v u).symm
  have hi := hinner (ketPi i)
  simpa [finiteKet_inner_eq_dotProduct, ketPi, Matrix.dotProduct] using hi

@[simp]
theorem matrixOfOp_adjoint [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : FinKetSpace ι →L[ℂ] FinKetSpace κ) :
    matrixOfOp (ContinuousLinearMap.adjoint T) = (matrixOfOp T)ᴴ := by
  apply matrixOp_injective (ι := κ) (κ := ι)
  rw [matrixOp_matrixOfOp, matrixOp_conjTranspose_eq_adjoint, matrixOp_matrixOfOp]

end CblinfunMatrix
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
