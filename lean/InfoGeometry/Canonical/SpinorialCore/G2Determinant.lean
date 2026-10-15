import InfoGeometry.Canonical.SpinorialCore.G2Certificate
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Signed determinant by triangular elimination

Witness source: `scripts/g2_relation_elimination.py`, reading the exact
`G2Certificate` adjacency in ascending `Fin 12` order. Only a matrix product
and triangular zero entries are evaluated; determinants are never expanded.
-/

namespace InfoGeometry.Canonical.SpinorialCore.G2

open Matrix

def elimination : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
     1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0;
     1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0;
     -1, -1, 1, 1, 1, -2, 1, 2, 0, 0, 0, 0;
     1, -1, -1, 1, 1, 0, 1, -2, 2, 0, 0, 0;
     -1, 3, -3, -7, -3, 2, -3, 2, -8, 4, 0, 0;
     -7, -1, 23, -27, -43, -8, 1, 14, 10, -60, 44, 0;
     -29, -25, -9, 55, -53, 19, -121, -15, 31, 33, -141, 73]

def triangularRelation : Matrix (Fin 12) (Fin 12) ℤ :=
  !![1, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1;
     0, 1, -1, 0, 0, 0, -1, -1, 0, 0, 0, 0;
     0, 0, 1, -1, 0, 0, 0, -1, -1, 0, 0, 0;
     0, 0, 0, 1, -1, 0, 0, 0, -1, -1, 0, 0;
     0, 0, 0, 0, 1, -1, 0, 0, 0, -1, -1, 0;
     0, 0, 0, 0, 0, -2, -2, -5, -4, -4, -2, -1;
     0, 0, 0, 0, 0, 0, -2, -2, -2, -2, -2, -2;
     0, 0, 0, 0, 0, 0, 0, 4, -4, -2, -2, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 4, -4, -2, -2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 2, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, -38;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 364]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem elimination_lower : elimination.BlockTriangular OrderDual.toDual := by
  letI : DecidableLT (Fin 12)ᵒᵈ := fun a b =>
    (inferInstance : Decidable (b.val < a.val))
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem triangularRelation_upper : triangularRelation.BlockTriangular id := by
  letI : DecidableLT (Fin 12) := fun a b =>
    (inferInstance : Decidable (a.val < b.val))
  decide

/-- Basis/orientation round trip for the CAS witness. -/
theorem elimination_basis_alignment :
    relation 0 1 = -1 ∧ relation (Equiv.swap (5 : Fin 12) 6 5) 0 = -1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem elimination_mul_relation :
    elimination * relation.submatrix (Equiv.swap 5 6) id = triangularRelation := by decide

theorem elimination_det : elimination.det = 51392 := by
  rw [Matrix.det_of_isLowerTriangular elimination elimination_lower]
  norm_num [elimination, Fin.prod_univ_succ]

theorem triangularRelation_det : triangularRelation.det = 74826752 := by
  rw [Matrix.det_of_isUpperTriangular triangularRelation_upper]
  norm_num [triangularRelation, Fin.prod_univ_succ]

/-- The sign comes from the single row swap, not just the Smith factors. -/
theorem relation_det : relation.det = -1456 := by
  have h := congrArg Matrix.det elimination_mul_relation
  rw [Matrix.det_mul, elimination_det, triangularRelation_det,
    Matrix.det_permute] at h
  rw [Equiv.Perm.sign_swap (show (5 : Fin 12) ≠ 6 by decide)] at h
  norm_num at h
  linarith

end InfoGeometry.Canonical.SpinorialCore.G2
