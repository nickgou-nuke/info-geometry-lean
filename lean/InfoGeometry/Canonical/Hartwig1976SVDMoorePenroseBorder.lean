import Mathlib.Tactic
import InfoGeometry.Canonical.MoorePenrose

/-!
# Hartwig 1976: SVD and Moore--Penrose inverses of bordered matrices

Source digest:

Robert E. Hartwig, "Singular Value Decomposition and the Moore--Penrose
Inverse of Bordered Matrices", SIAM Journal on Applied Mathematics 31(1),
31--41, 1976.

Hartwig reduces the bordered matrix

`M = [[A, c], [b*, d]]`

by singular-value decomposition of `A`.  The resulting small block problem is
split by the kernel components of `b` and `c` and by the generalized Schur
complement `z = d - b* A+ c`.  This file formalizes exact rational witnesses
for two of the paper's structural regimes:

* Case 1: `b` and `c` lie in the row/column ranges of `A` and `z ≠ 0`.
* Case 3: both border vectors have nonzero kernel components, so the rank jumps.

For each packet we prove the Moore--Penrose laws for the bordered matrix and
for the associated principal Schur complement.  We also check that the bordered
Moore--Penrose packet is stable under a strict finite orthogonal permutation
representative.

The file intentionally does not formalize floating-point SVD algorithms,
analytic perturbation bounds, or the full five-case symbolic formula table.
Those are represented by exact external certificates in `tools/`.
-/

noncomputable section

namespace InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder

open InfoGeometry.Canonical

abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R
abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-! ## SVD-reduced base matrix -/

/-- SVD-reduced rank-one base block: one singular value `2` and one zero lane. -/
def baseA : Mat2 ℚ :=
  !![2, 0;
     0, 0]

/-- Moore--Penrose inverse of the SVD-reduced base block. -/
def baseAMP : Mat2 ℚ :=
  !![1 / 2, 0;
     0, 0]

/-- The base SVD packet satisfies the Moore--Penrose equations. -/
theorem baseA_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse baseA baseAMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-! ## Hartwig Case 1: `b,c` in range and `z ≠ 0` -/

/--
Case 1 bordered matrix:

`A = diag(2,0)`, `c = (3,0)^T`, `b = (1,0)^T`, `d = 5`.

Here `z = d - b* A+ c = 7/2`, while the zero singular lane remains untouched.
-/
def case1Border : Mat3 ℚ :=
  !![2, 0, 3;
     0, 0, 0;
     1, 0, 5]

/-- Hartwig Case 1 formula with `z = 7/2`. -/
def case1BorderMP : Mat3 ℚ :=
  !![5 / 7, 0, -3 / 7;
     0, 0, 0;
     -1 / 7, 0, 2 / 7]

/-- The generalized Schur complement scalar in Case 1 is nonzero. -/
def case1Z : ℚ :=
  5 - (1 : ℚ) * (1 / 2) * 3

/-- `z = d - b* A+ c = 7/2`. -/
theorem case1Z_eq :
    case1Z = 7 / 2 := by
  norm_num [case1Z]

/-- Hartwig's Case 1 bordered witness satisfies the Moore--Penrose equations. -/
theorem case1Border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case1Border case1BorderMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Associated principal Schur complement `A - c d⁻¹ b*` for Case 1. -/
def case1Schur : Mat2 ℚ :=
  !![7 / 5, 0;
     0, 0]

/-- Moore--Penrose inverse of the Case 1 Schur complement. -/
def case1SchurMP : Mat2 ℚ :=
  !![5 / 7, 0;
     0, 0]

/-- The Case 1 Schur-complement witness satisfies the Moore--Penrose equations. -/
theorem case1Schur_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case1Schur case1SchurMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-! ## Hartwig Case 3: both border vectors have kernel components -/

/--
Case 3-style packet:

`A = diag(2,0)`, `c = (0,1)^T`, `b = (0,1)^T`, `d = 5`.

The border vectors live in the zero singular lane, so the bordered matrix has
full rank even though the principal block is singular.
-/
def case3Border : Mat3 ℚ :=
  !![2, 0, 0;
     0, 0, 1;
     0, 1, 5]

/-- Moore--Penrose inverse of the full-rank Case 3 bordered matrix. -/
def case3BorderMP : Mat3 ℚ :=
  !![1 / 2, 0, 0;
     0, -5, 1;
     0, 1, 0]

/-- The Case 3 bordered witness satisfies the Moore--Penrose equations. -/
theorem case3Border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case3Border case3BorderMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Associated principal Schur complement `A - c d⁻¹ b*` for Case 3. -/
def case3Schur : Mat2 ℚ :=
  !![2, 0;
     0, -1 / 5]

/-- Moore--Penrose inverse of the Case 3 Schur complement. -/
def case3SchurMP : Mat2 ℚ :=
  !![1 / 2, 0;
     0, -5]

/-- The Case 3 Schur-complement witness satisfies the Moore--Penrose equations. -/
theorem case3Schur_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case3Schur case3SchurMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-! ## Strict finite orthogonal group representative -/

/-- A permutation matrix, used as a rational orthogonal representative. -/
def borderPermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The permutation representative squares to the identity. -/
theorem borderPermutation_sq_eq_one :
    borderPermutation * borderPermutation = 1 := by
  native_decide

/-- The permutation representative is self-adjoint. -/
theorem borderPermutation_star_eq_self :
    star borderPermutation = borderPermutation := by
  native_decide

/-- The permutation as a strict unit of the matrix algebra. -/
def borderPermutationUnit : (Mat3 ℚ)ˣ where
  val := borderPermutation
  inv := borderPermutation
  val_inv := borderPermutation_sq_eq_one
  inv_val := borderPermutation_sq_eq_one

/-- Unit conjugation on the finite bordered matrix algebra. -/
def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

/-- Hartwig's Case 1 Moore--Penrose witness is stable under the permutation action. -/
theorem case1_conjugated_border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse
      (unitConj borderPermutationUnit case1Border)
      (unitConj borderPermutationUnit case1BorderMP) := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder
