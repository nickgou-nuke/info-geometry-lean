/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralOrder
import InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralReynolds
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The integral Reynolds image in the concrete matrix order

The cut `E₀₀` and amplitudes `E₀₁`, `v E₁₀` recover exactly the existing
Peirce corners and have mass `v * I`. The existing integral Reynolds
operator on an arbitrary full matrix `M` is the scalar matrix with entry
`2 * v² * (M 0 0 + M 1 1)`.

Its image on `parameterOrder v` is exactly the scalar matrices whose entry
is a multiple of `2 * v²`. The preimage of such a scalar is `r E₀₀`, which
belongs to the order for every `r`. In particular, over a nontrivial
polynomial coefficient ring with `v = X`, the identity is not in the image.
These statements concern the concrete order, without a universal-presentation
or ambient-center assertion for arbitrary Peirce realizations.
-/

set_option autoImplicit false

open Polynomial

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralOrder

variable {R : Type*} [CommRing R]

local notation "Mat₂" => Matrix (Fin 2) (Fin 2) R

/-- The native matrix cut is idempotent. -/
theorem matrixCut_idempotent :
    (Matrix.single 0 0 (1 : R) : Mat₂) * Matrix.single 0 0 (1 : R) =
      Matrix.single 0 0 (1 : R) := by
  simp

/-- The chosen upper amplitude is exactly its upper Peirce corner. -/
theorem matrix_conePlus :
    conePlus (Matrix.single 0 0 (1 : R) : Mat₂) (Matrix.single 0 1 (1 : R)) =
      Matrix.single 0 1 (1 : R) := by
  simp [conePlus, mul_sub]

/-- The chosen lower amplitude is exactly its lower Peirce corner. -/
theorem matrix_coneMinus (v : R) :
    coneMinus (Matrix.single 0 0 (1 : R) : Mat₂) (Matrix.single 1 0 v) =
      Matrix.single 1 0 v := by
  simp [coneMinus, sub_mul]

/-- The Peirce mass is the scalar parameter in this concrete model. -/
theorem matrix_genV (v : R) :
    genV (Matrix.single 0 0 (1 : R) : Mat₂)
        (Matrix.single 0 1 (1 : R)) (Matrix.single 1 0 v) =
      algebraMap R Mat₂ v := by
  simp only [genV, anticomm, matrix_conePlus, matrix_coneMinus]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      Matrix.algebraMap_matrix_apply]

/-- The exact integral Reynolds formula on every full two-by-two matrix. -/
theorem matrix_integralReynolds (v : R) (M : Mat₂) :
    integralReynolds (Matrix.single 0 0 (1 : R) : Mat₂)
        (Matrix.single 0 1 (1 : R)) (Matrix.single 1 0 v) M =
      algebraMap R Mat₂ (2 * v ^ 2 * (M 0 0 + M 1 1)) := by
  rw [integralReynolds_eq_sandwich]
  simp only [matrix_genV, genPhi, genJ, genSig, comm, matrix_conePlus, matrix_coneMinus]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      Matrix.algebraMap_matrix_apply, pow_two] <;> ring

/-- Every scalar multiple of `2 * v²` occurs, and these are all the outputs
on the concrete order. No division or coefficient cancellation is used. -/
theorem integralReynolds_range_parameterOrder (v : R) :
    Set.range (fun M : parameterOrder v =>
      integralReynolds (Matrix.single 0 0 (1 : R) : Mat₂)
        (Matrix.single 0 1 (1 : R)) (Matrix.single 1 0 v) (M : Mat₂)) =
      Set.range (fun r : R => algebraMap R Mat₂ (2 * v ^ 2 * r)) := by
  apply Set.ext
  intro Y
  constructor
  · rintro ⟨M, rfl⟩
    refine ⟨(M : Mat₂) 0 0 + (M : Mat₂) 1 1, ?_⟩
    exact (matrix_integralReynolds v (M : Mat₂)).symm
  · rintro ⟨r, rfl⟩
    have hm : (Matrix.single 0 0 r : Mat₂) ∈ parameterOrder v := by
      simp [mem_parameterOrder, Matrix.single_apply]
    refine ⟨⟨Matrix.single 0 0 r, hm⟩, ?_⟩
    rw [matrix_integralReynolds]
    simp [Matrix.single_apply]

/-- Over a nontrivial polynomial ring the integral Reynolds image misses
the identity, so it is not all scalar matrices. This applies to `ℤ[X]`. -/
theorem one_not_mem_integralReynolds_range_polynomialOrder [Nontrivial R] :
    (1 : Matrix (Fin 2) (Fin 2) R[X]) ∉
      Set.range (fun M : polynomialOrder R =>
        integralReynolds
          (Matrix.single 0 0 (1 : R[X]) : Matrix (Fin 2) (Fin 2) R[X])
          (Matrix.single 0 1 (1 : R[X])) (Matrix.single 1 0 (X : R[X]))
          (M : Matrix (Fin 2) (Fin 2) R[X])) := by
  rintro ⟨M, hM⟩
  rw [matrix_integralReynolds] at hM
  have hzero := congrArg
    (fun N : Matrix (Fin 2) (Fin 2) R[X] => Polynomial.eval (0 : R) (N 0 0)) hM
  simpa [Matrix.algebraMap_matrix_apply, Matrix.one_apply] using hzero

end InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralOrder
