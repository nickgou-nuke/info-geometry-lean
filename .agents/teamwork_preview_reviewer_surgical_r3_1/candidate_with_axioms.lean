import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

lemma baseA_mul_baseAMP :
    baseA * baseAMP = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, baseA, baseAMP]

lemma baseAMP_mul_baseA :
    baseAMP * baseA = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, baseA, baseAMP]

/-- The base SVD packet satisfies the Moore--Penrose equations. -/
theorem baseA_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse baseA baseAMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [baseA_mul_baseAMP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, baseA]
  · rw [baseAMP_mul_baseA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, baseAMP]
  · rw [baseA_mul_baseAMP]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [baseAMP_mul_baseA]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

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

lemma case1Border_mul_case1BorderMP :
    case1Border * case1BorderMP = !![1, 0, 0; 0, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, case1Border, case1BorderMP]; try norm_num)

lemma case1BorderMP_mul_case1Border :
    case1BorderMP * case1Border = !![1, 0, 0; 0, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, case1Border, case1BorderMP]; try norm_num)

/-- Hartwig's Case 1 bordered witness satisfies the Moore--Penrose equations. -/
theorem case1Border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case1Border case1BorderMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [case1Border_mul_case1BorderMP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, case1Border]
  · rw [case1BorderMP_mul_case1Border]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, case1BorderMP]
  · rw [case1Border_mul_case1BorderMP]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [case1BorderMP_mul_case1Border]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- Associated principal Schur complement `A - c d⁻¹ b*` for Case 1. -/
def case1Schur : Mat2 ℚ :=
  !![7 / 5, 0;
     0, 0]

/-- Moore--Penrose inverse of the Case 1 Schur complement. -/
def case1SchurMP : Mat2 ℚ :=
  !![5 / 7, 0;
     0, 0]

lemma case1Schur_mul_case1SchurMP :
    case1Schur * case1SchurMP = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, case1Schur, case1SchurMP]

lemma case1SchurMP_mul_case1Schur :
    case1SchurMP * case1Schur = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, case1Schur, case1SchurMP]

/-- The Case 1 Schur-complement witness satisfies the Moore--Penrose equations. -/
theorem case1Schur_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case1Schur case1SchurMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [case1Schur_mul_case1SchurMP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, case1Schur]
  · rw [case1SchurMP_mul_case1Schur]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, case1SchurMP]
  · rw [case1Schur_mul_case1SchurMP]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [case1SchurMP_mul_case1Schur]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

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

lemma case3Border_mul_case3BorderMP :
    case3Border * case3BorderMP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, case3Border, case3BorderMP]

lemma case3BorderMP_mul_case3Border :
    case3BorderMP * case3Border = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, case3Border, case3BorderMP]

/-- The Case 3 bordered witness satisfies the Moore--Penrose equations. -/
theorem case3Border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case3Border case3BorderMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [case3Border_mul_case3BorderMP, one_mul]
  · rw [case3BorderMP_mul_case3Border, one_mul]
  · rw [case3Border_mul_case3BorderMP, star_one]
  · rw [case3BorderMP_mul_case3Border, star_one]

/-- Associated principal Schur complement `A - c d⁻¹ b*` for Case 3. -/
def case3Schur : Mat2 ℚ :=
  !![2, 0;
     0, -1 / 5]

/-- Moore--Penrose inverse of the Case 3 Schur complement. -/
def case3SchurMP : Mat2 ℚ :=
  !![1 / 2, 0;
     0, -5]

lemma case3Schur_mul_case3SchurMP :
    case3Schur * case3SchurMP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two, case3Schur, case3SchurMP]; try norm_num)

lemma case3SchurMP_mul_case3Schur :
    case3SchurMP * case3Schur = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two, case3Schur, case3SchurMP]; try norm_num)

/-- The Case 3 Schur-complement witness satisfies the Moore--Penrose equations. -/
theorem case3Schur_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse case3Schur case3SchurMP := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [case3Schur_mul_case3SchurMP, one_mul]
  · rw [case3SchurMP_mul_case3Schur, one_mul]
  · rw [case3Schur_mul_case3SchurMP, star_one]
  · rw [case3SchurMP_mul_case3Schur, star_one]

/-! ## Strict finite orthogonal group representative -/

/-- A permutation matrix, used as a rational orthogonal representative. -/
def borderPermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The permutation representative squares to the identity. -/
theorem borderPermutation_sq_eq_one :
    borderPermutation * borderPermutation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, borderPermutation]

/-- The permutation representative is self-adjoint. -/
theorem borderPermutation_star_eq_self :
    star borderPermutation = borderPermutation := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The permutation as a strict unit of the matrix algebra. -/
def borderPermutationUnit : (Mat3 ℚ)ˣ where
  val := borderPermutation
  inv := borderPermutation
  val_inv := borderPermutation_sq_eq_one
  inv_val := borderPermutation_sq_eq_one

/-- Unit conjugation on the finite bordered matrix algebra. -/
def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

theorem unitConj_isMoorePenrose (u : (Mat3 ℚ)ˣ) (A X : Mat3 ℚ)
    (hu_star : star (u : Mat3 ℚ) = ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
    (h : MoorePenrose.IsMoorePenroseInverse A X) :
    MoorePenrose.IsMoorePenroseInverse (unitConj u A) (unitConj u X) := by
  have hu_inv_star : star (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) = (u : Mat3 ℚ) := by
    rw [← hu_star, star_star]
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · unfold unitConj
    have h1 : (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
        = (u : Mat3 ℚ) * (A * X * A) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      calc
        (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
          = (u : Mat3 ℚ) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * X * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [mul_assoc]
        _ = (u : Mat3 ℚ) * (A * X * A) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [Units.inv_mul, mul_one, mul_assoc]
    rw [h1, h.1]
  · unfold unitConj
    have h2 : (u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
        = (u : Mat3 ℚ) * (X * A * X) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      calc
        (u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
          = (u : Mat3 ℚ) * X * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [mul_assoc]
        _ = (u : Mat3 ℚ) * (X * A * X) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [Units.inv_mul, mul_one, mul_assoc]
    rw [h2, h.2.1]
  · unfold unitConj
    have h3 : (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
        = (u : Mat3 ℚ) * (A * X) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      calc
        (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
          = (u : Mat3 ℚ) * A * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [mul_assoc]
        _ = (u : Mat3 ℚ) * (A * X) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [Units.inv_mul, mul_one, mul_assoc]
    rw [h3, star_mul, star_mul, hu_inv_star, hu_star, h.2.2.1]
    simp only [mul_assoc]
  · unfold unitConj
    have h4 : (u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
        = (u : Mat3 ℚ) * (X * A) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
      calc
        (u : Mat3 ℚ) * X * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * ((u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ))
          = (u : Mat3 ℚ) * X * (((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) * (u : Mat3 ℚ)) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [mul_assoc]
        _ = (u : Mat3 ℚ) * (X * A) * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ) := by
          simp only [Units.inv_mul, mul_one, mul_assoc]
    rw [h4, star_mul, star_mul, hu_inv_star, hu_star, h.2.2.2]
    simp only [mul_assoc]

/-- Hartwig's Case 1 Moore--Penrose witness is stable under the permutation action. -/
theorem case1_conjugated_border_isMoorePenrose :
    MoorePenrose.IsMoorePenroseInverse
      (unitConj borderPermutationUnit case1Border)
      (unitConj borderPermutationUnit case1BorderMP) :=
  unitConj_isMoorePenrose borderPermutationUnit case1Border case1BorderMP
    borderPermutation_star_eq_self case1Border_isMoorePenrose


#print axioms baseA_isMoorePenrose
#print axioms case1Z_eq
#print axioms case1Border_isMoorePenrose
#print axioms case1Schur_isMoorePenrose
#print axioms case3Border_isMoorePenrose
#print axioms case3Schur_isMoorePenrose
#print axioms borderPermutation_sq_eq_one
#print axioms borderPermutation_star_eq_self
#print axioms unitConj_isMoorePenrose
#print axioms case1_conjugated_border_isMoorePenrose

end InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder
