/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import InfoGeometry.Supergeometry.BerezinianDecomposition

/-!
# Ordered Schur factorization and the ordinary-coefficient ratio boundary

The factorization below allows arbitrary rectangular off-diagonal blocks and
an associative, possibly noncommutative coefficient ring. Both inverse laws
are explicit. Ordinary determinants are used only in the commutative
coefficient specialization.

The existing scalar Schur-ratio owner is also tested on actual rational
matrices: its value is not multiplicative on unrestricted ordinary matrices.
Consequently the factorization does not by itself construct a multiplicative
Berezinian over a supercommutative coefficient algebra.
-/

namespace InfoGeometry.Algebra.BlockSchurFactorization

open Matrix

section Ring

variable {R l m n : Type*} [Ring R]
  [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- Upper–diagonal–lower factorization about the bottom-right block. The
coefficient ring need not be commutative, and `A` need not be square. -/
theorem fromBlocks_eq_ordered_schur
    (A : Matrix l m R) (B : Matrix l n R) (C : Matrix n m R)
    (D Dinv : Matrix n n R)
    (hleft : Dinv * D = 1) (hright : D * Dinv = 1) :
    fromBlocks A B C D =
      fromBlocks (1 : Matrix l l R) (B * Dinv) 0 (1 : Matrix n n R) *
        fromBlocks (A - B * Dinv * C) 0 0 D *
          fromBlocks (1 : Matrix m m R) 0 (Dinv * C) (1 : Matrix n n R) := by
  have hBD : B * Dinv * D = B := by
    rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  have hDC : D * (Dinv * C) = C := by
    rw [← Matrix.mul_assoc, hright, Matrix.one_mul]
  symm
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, hBD, hDC]
  rw [← Matrix.mul_assoc B Dinv C, sub_add_cancel]

end Ring

section Determinant

variable {R m n : Type*} [CommRing R]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The native ordinary determinant follows from the ordered factorization;
it multiplies the two diagonal determinants. -/
theorem det_fromBlocks_eq_schur_mul_det
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D Dinv : Matrix n n R)
    (hleft : Dinv * D = 1) (hright : D * Dinv = 1) :
    (fromBlocks A B C D).det = (A - B * Dinv * C).det * D.det := by
  rw [fromBlocks_eq_ordered_schur A B C D Dinv hleft hright]
  simp only [Matrix.det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂,
    det_one, one_mul, mul_one]

end Determinant

/-- Lower triangular matrix used in the ordinary Schur-ratio counterexample. -/
def schurLower : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 1, 1]

/-- Upper triangular matrix used in the ordinary Schur-ratio counterexample. -/
def schurUpper : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

/-- Reversing the actual two factors changes their product. -/
theorem schur_triangular_noncommute :
    schurLower * schurUpper ≠ schurUpper * schurLower := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num [schurLower, schurUpper, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- All three denominator choices are genuine inverses, but the existing
ordinary-coefficient Schur ratio changes from `1*1` to `1/4` under this product.
This refutes unrestricted multiplicativity without altering the ratio owner. -/
theorem scalar_schur_ratio_counterexample :
    let L := schurLower
    let U := schurUpper
    Supergeometry.Berezinian.isRegularD L 1 ∧
      Supergeometry.Berezinian.isRegularD U 1 ∧
      Supergeometry.Berezinian.isRegularD (L * U) (1 / 2) ∧
      Supergeometry.Berezinian.berezinian (L * U) (1 / 2) = 1 / 4 ∧
      Supergeometry.Berezinian.berezinian (L * U) (1 / 2) ≠
        Supergeometry.Berezinian.berezinian L 1 *
          Supergeometry.Berezinian.berezinian U 1 := by
  norm_num [schurLower, schurUpper, Supergeometry.Berezinian.isRegularD,
    Supergeometry.Berezinian.berezinian, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Algebra.BlockSchurFactorization
