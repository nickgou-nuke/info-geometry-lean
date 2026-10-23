/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SuperGrassmannianSusy
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

/-!
# Characteristic-two boundary for reflection/tangent equivalence

The reflection identity is always twice the Grassmannian tangent defect.  It
therefore cannot characterize tangency without an injectivity hypothesis for
doubling.  This file records an explicit kernel-checked counterexample over
`ZMod 2`, so the repaired theorem in `PeirceTangent` has a concrete boundary
case rather than an informal characteristic warning.
-/

namespace InfoGeometry.Core.PeirceTangent

open InfoGeometry.Core.SuperGrassmannianSusy

def matrixBoundaryProjection : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 0, 0]
def matrixBoundaryDirection : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 0]

/-- A genuine noncommuting matrix boundary case, with an idempotent endpoint.
Reflection anticommutation does not eliminate its nonzero diagonal corner. -/
theorem matrix_reflection_anticommutation_not_tangent :
    matrixBoundaryProjection * matrixBoundaryProjection = matrixBoundaryProjection ∧
      matrixBoundaryProjection * matrixBoundaryDirection ≠
        matrixBoundaryDirection * matrixBoundaryProjection ∧
      ¬ IsGrassmannianTangent matrixBoundaryProjection matrixBoundaryDirection ∧
      (2 * matrixBoundaryProjection - 1) * matrixBoundaryDirection +
        matrixBoundaryDirection * (2 * matrixBoundaryProjection - 1) = 0 := by
  let p := matrixBoundaryProjection
  have hpp : p * p = p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [p, matrixBoundaryProjection, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨hpp, ?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun C : Matrix (Fin 2) (Fin 2) (ZMod 2) => C 0 1) h
    norm_num [matrixBoundaryProjection, matrixBoundaryDirection, Matrix.mul_apply,
      Fin.sum_univ_succ] at he
  · intro h
    have he := congrArg (fun C : Matrix (Fin 2) (Fin 2) (ZMod 2) => C 0 0) h
    norm_num [IsGrassmannianTangent, jordanProd, matrixBoundaryProjection,
      matrixBoundaryDirection, Matrix.mul_apply, Fin.sum_univ_succ] at he
    contradiction
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [matrixBoundaryProjection, matrixBoundaryDirection, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> decide

#print axioms matrix_reflection_anticommutation_not_tangent

/-- Doubling is not injective in characteristic two. -/
theorem zmodTwo_doubling_not_injective :
    ¬ Function.Injective (fun y : ZMod 2 => (2 : ℕ) • y) := by
  intro h
  have h01 : (0 : ZMod 2) = 1 := by
    apply h
    decide
  norm_num at h01

/-- In characteristic two, reflection anticommutation can hold while the
first-order idempotent/tangent equation fails. -/
theorem zmodTwo_reflection_anticommutation_not_tangent :
    (¬ IsGrassmannianTangent (0 : ZMod 2) 1) ∧
      ((2 * (0 : ZMod 2) - 1) * 1 +
          1 * (2 * (0 : ZMod 2) - 1) = 0) := by
  constructor
  · intro h
    norm_num [IsGrassmannianTangent, jordanProd] at h
  · decide

/-- The counterexample is exactly the failure of the missing doubling
injectivity premise in the reflection characterization. -/
theorem zmodTwo_reflection_boundary :
    ¬ Function.Injective (fun y : ZMod 2 => (2 : ℕ) • y) ∧
      (¬ IsGrassmannianTangent (0 : ZMod 2) 1 ∧
        ((2 * (0 : ZMod 2) - 1) * 1 +
            1 * (2 * (0 : ZMod 2) - 1) = 0)) := by
  exact ⟨zmodTwo_doubling_not_injective,
    zmodTwo_reflection_anticommutation_not_tangent⟩

end InfoGeometry.Core.PeirceTangent
