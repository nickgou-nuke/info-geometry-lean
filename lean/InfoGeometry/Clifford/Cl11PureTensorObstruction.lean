/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedUnrolling
import InfoGeometry.Algebra.MatrixRankFactorization
import Mathlib.Data.Matrix.Composition

/-!
# A matrix which requires a sum of graded Clifford tensor chains

The native graded tensor `(1+η)/2 ⊗ 1 + (1-η)/2 ⊗ K` maps to the controlled
`K` block matrix. Two native linear coordinate functionals on each factor
give a two-by-two identity minor. Every simple tensor instead gives an outer
product, so this tensor cannot be a single graded tensor.

This is a statement about the actual Clifford factors and their native graded
tensor product, not merely a determinant of an unrelated coefficient array.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11PureTensorObstruction

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedUnrolling
open InfoGeometry.Algebra.MatrixRankFactorization

abbrev C := CliffordAlgebra q11
abbrev Pair := CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd q11

def positiveCorner : C := (1 / 2 : ℝ) • (1 + CliffordAlgebra.ι q11 (1, 0))

def negativeCorner : C := (1 / 2 : ℝ) • (1 - CliffordAlgebra.ι q11 (1, 0))

def controlledTensor : Pair :=
  (positiveCorner ᵍ⊗ₜ (1 : C)) + (negativeCorner ᵍ⊗ₜ J1_cl)

/-- Diagonal coordinates distinguish the two head corners. -/
def headCoordinate (i : Fin 2) : C →ₗ[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i i).comp cl11EquivMat.toLinearMap

/-- The first row distinguishes the even tail elements `1` and `K`. -/
def tailCoordinate (j : Fin 2) : C →ₗ[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ 0 j).comp cl11EquivMat.toLinearMap

/-- A genuine linear readout of the underlying native tensor carrier. -/
def tensorMinor : Pair →ₗ[ℝ] Mat2 :=
  LinearMap.pi fun i => LinearMap.pi fun j =>
    ((TensorProduct.lid ℝ ℝ).toLinearMap.comp
      (TensorProduct.map (headCoordinate i) (tailCoordinate j))).comp
        (GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11)
          (CliffordAlgebra.evenOdd q11)).symm.toLinearMap

@[simp] theorem tensorMinor_tmul (x y : C) (i j : Fin 2) :
    tensorMinor (x ᵍ⊗ₜ y) i j = headCoordinate i x * tailCoordinate j y := by
  change (TensorProduct.lid ℝ ℝ)
    (TensorProduct.map (headCoordinate i) (tailCoordinate j)
      ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11)
        (CliffordAlgebra.evenOdd q11)).symm (x ᵍ⊗ₜ y))) = _
  simp [GradedTensorProduct.tmul]

theorem tensorMinor_controlled : tensorMinor controlledTensor = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controlledTensor, map_add, tensorMinor_tmul, headCoordinate,
      tailCoordinate, positiveCorner, negativeCorner, J1_cl, map_mul,
      Eplus_mul_Eminus, Eplus, Eminus, J1, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- The controlled-`K` tensor is not one graded product, even when its two
factors are allowed to be arbitrary inhomogeneous Clifford elements. -/
theorem controlledTensor_not_simple :
    ¬ ∃ x y : C, controlledTensor = x ᵍ⊗ₜ y := by
  rintro ⟨x, y, hxy⟩
  have hminor := not_pure_of_cross_mul_ne (1 : Mat2) 0 1 0 1 (by norm_num)
  apply hminor
  refine ⟨fun i => headCoordinate i x, fun j => tailCoordinate j y, ?_⟩
  intro i j
  have h := congrArg (fun T : Pair => tensorMinor T i j) hxy
  simpa [tensorMinor_controlled] using h

private theorem parity_even {a : C} (ha : a ∈ CliffordAlgebra.evenOdd q11 0) :
    CliffordAlgebra.involuteEquiv a = a :=
  CliffordAlgebra.involute_eq_of_mem_even ha

private theorem parity_odd {a : C} (ha : a ∈ CliffordAlgebra.evenOdd q11 1) :
    CliffordAlgebra.involuteEquiv a = -a :=
  CliffordAlgebra.involute_eq_of_mem_odd ha

/-- The faithful two-factor readout, retaining the original local basis. -/
def pairMatrixEquiv : Pair ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) Mat2 :=
  (tensorMatrixEquivOriginal CliffordAlgebra.involuteEquiv
    (CliffordAlgebra.evenOdd q11) parity_even parity_odd).trans
      cl11EquivMat.mapMatrix

/-- The obstruction's matrix is exactly the intake's diagonal `I,K` blocks. -/
theorem pairMatrixEquiv_controlled :
    pairMatrixEquiv controlledTensor = !![1, 0; 0, J1] := by
  change (tensorMatrixEquivOriginal CliffordAlgebra.involuteEquiv
    (CliffordAlgebra.evenOdd q11) parity_even parity_odd controlledTensor).map
      cl11EquivMat = _
  simp only [controlledTensor, map_add, tensorMatrixEquivOriginal_tmul_entries]
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [evenPart, oddPart, positiveCorner, negativeCorner, J1_cl,
      CliffordAlgebra.involuteEquiv, CliffordAlgebra.involute_ι,
      map_mul, map_ofNat, Matrix.ofNat_apply, Eplus_mul_Eminus, Eplus, Eminus, J1]

/-- A concrete four-by-four matrix (written in two-by-two blocks) has no
single graded Clifford factorization. Singular/invertible input restrictions
play no role in this obstruction. -/
theorem controlledMatrix_not_single_chain :
    ¬ ∃ x y : C, pairMatrixEquiv (x ᵍ⊗ₜ y) = !![1, 0; 0, J1] := by
  rintro ⟨x, y, hxy⟩
  apply controlledTensor_not_simple
  refine ⟨x, y, ?_⟩
  apply pairMatrixEquiv.injective
  rw [pairMatrixEquiv_controlled, hxy]

end InfoGeometry.Clifford.Cl11PureTensorObstruction
