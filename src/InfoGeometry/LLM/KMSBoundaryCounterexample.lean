/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A finite Kac–Murdock–Szegő boundary counterexample

The exact rational three-site kernel at parameter `1/2` has a tridiagonal
two-sided inverse with unequal endpoint and interior diagonals. It does not
commute with the standard three-site Dirichlet second-difference matrix.
These are full matrix statements; no general spectral or Lie-algebra
classification is asserted.
-/

namespace InfoGeometry.LLM.KMSBoundaryCounterexample

open Matrix

/-- The three-site KMS kernel at parameter `1/2`. -/
def kmsThree : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1 / 2, 1 / 4; 1 / 2, 1, 1 / 2; 1 / 4, 1 / 2, 1]

/-- The exact precision matrix, including its endpoint correction. -/
def kmsThreeInverse : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4 / 3, -2 / 3, 0; -2 / 3, 5 / 3, -2 / 3; 0, -2 / 3, 4 / 3]

/-- The standard three-site Dirichlet second-difference matrix. -/
def dirichletThree : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2, -1, 0; -1, 2, -1; 0, -1, 2]

/-- The displayed matrix is exactly the exponential-distance kernel. -/
theorem kmsThree_apply (i j : Fin 3) :
    kmsThree i j = (1 / 2 : ℚ) ^ Nat.dist i.val j.val := by
  fin_cases i <;> fin_cases j <;> norm_num [kmsThree, Nat.dist]

/-- The proposed inverse is a right inverse of the full KMS matrix. -/
theorem kmsThree_mul_inverse : kmsThree * kmsThreeInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kmsThree, kmsThreeInverse, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The proposed inverse is also a left inverse. -/
theorem inverse_mul_kmsThree : kmsThreeInverse * kmsThree = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kmsThree, kmsThreeInverse, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Endpoint and interior diagonal entries of the precision matrix differ. -/
theorem inverse_endpoint_ne_interior :
    kmsThreeInverse 0 0 ≠ kmsThreeInverse 1 1 := by
  norm_num [kmsThreeInverse]

/-- A concrete entry detects failure to commute with the Dirichlet matrix. -/
theorem kmsThree_dirichlet_commutator_entry :
    (kmsThree * dirichletThree - dirichletThree * kmsThree) 0 1 = -1 / 4 := by
  norm_num [kmsThree, dirichletThree, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A KMS matrix need not commute with the standard Dirichlet matrix. -/
theorem kmsThree_mul_dirichlet_ne :
    kmsThree * dirichletThree ≠ dirichletThree * kmsThree := by
  intro h
  have he := kmsThree_dirichlet_commutator_entry
  rw [h, sub_self] at he
  norm_num at he

/-- Even an affine rescaling of the standard Dirichlet matrix misses the endpoints. -/
theorem inverse_ne_affine_dirichlet (a b : ℚ) :
    kmsThreeInverse ≠ a • dirichletThree + b • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by
  intro h
  apply inverse_endpoint_ne_interior
  rw [h]
  norm_num [dirichletThree]

end InfoGeometry.LLM.KMSBoundaryCounterexample
