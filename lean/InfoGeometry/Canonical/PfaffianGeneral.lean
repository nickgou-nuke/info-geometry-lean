import Mathlib

/-!
# InfoGeometry.Canonical.PfaffianGeneral

General $2n \times 2n$ skew-symmetric block-diagonal Pfaffian construction.

This file generalizes the $2 \times 2$ Pfaffian identity $\text{Pf}(M)^2 = \det(M)$
to arbitrary $2n \times 2n$ block skew-symmetric matrices over any commutative ring,
establishing the algebraic core for Class D topological phase invariants ($\mathbb{Z}_2$).
-/

namespace InfoGeometry.Canonical.PfaffianGeneral

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Standard 2×2 skew-symmetric block with value `a`. -/
def skewBlock2x2 (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, a; -a, 0]

@[simp] theorem det_skewBlock2x2 (a : R) :
    (skewBlock2x2 a).det = a ^ 2 := by
  simp [skewBlock2x2, Matrix.det_fin_two, pow_two]

/--
A canonical $2n \times 2n$ block skew-symmetric matrix formed by $n$ diagonal
$2 \times 2$ blocks with entries $a_i$.
-/
def blockSkewMatrix (n : ℕ) (a : Fin n → R) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) R :=
  Matrix.blockDiagonal (fun i => skewBlock2x2 (a i))

/-- The $2n \times 2n$ Pfaffian of a block skew-symmetric matrix is the product of block values. -/
def pfaffianBlock (n : ℕ) (a : Fin n → R) : R :=
  ∏ i : Fin n, a i

/--
**General Pfaffian Determinant Identity:**
For any $2n \times 2n$ block skew-symmetric matrix $M$, $\text{Pf}(M)^2 = \det(M)$.
-/
theorem pfaffian_sq_eq_det_general (n : ℕ) (a : Fin n → R) :
    (pfaffianBlock n a) ^ 2 = (blockSkewMatrix n a).det := by
  unfold blockSkewMatrix pfaffianBlock
  rw [Matrix.det_blockDiagonal]
  simp only [det_skewBlock2x2]
  rw [← Finset.prod_pow]

/--
**Determinant Nonnegativity for Real Skew Matrices:**
For any real $2n \times 2n$ block skew-symmetric matrix, $\det(M) \ge 0$.
-/
theorem det_blockSkewMatrix_nonneg (n : ℕ) (a : Fin n → ℝ) :
    0 ≤ (blockSkewMatrix n a).det := by
  rw [← pfaffian_sq_eq_det_general]
  exact sq_nonneg _

/--
**Pfaffian Multiplicativity:**
The block Pfaffian distributes over point-wise multiplication of diagonal blocks.
-/
theorem pfaffianBlock_mul (n : ℕ) (a b : Fin n → R) :
    pfaffianBlock n (fun i => a i * b i) = pfaffianBlock n a * pfaffianBlock n b := by
  unfold pfaffianBlock
  exact Finset.prod_mul_distrib

end InfoGeometry.Canonical.PfaffianGeneral
