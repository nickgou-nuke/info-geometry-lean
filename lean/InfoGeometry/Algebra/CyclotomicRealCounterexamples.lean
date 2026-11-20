/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.LieCyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
import InfoGeometry.Algebra.Quantum.QBinomial

noncomputable section

/-!
Exact real operator counterexamples to three overstrong implications in the
intake. The nested `2 × 2` matrices act on a real four-dimensional space.
All coefficients and operators are real; no scalar imaginary unit occurs.

This focused owner reuses the real companion and native quantum-binomial
coefficient. These finite counterexamples constrain general claims; they do
not construct a connection, curvature tensor, Kähler structure, or gauge theory.
-/

namespace InfoGeometry.Algebra.CyclotomicRealCounterexamples

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Algebra.LieCyclotomicBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
open scoped Matrix

/-- The native real third-root companion already has zero cyclic sum. -/
theorem thirdRoot_cyclic_sum_zero : (1 : Mat2) + thirdRoot + thirdRoot ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thirdRoot, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- Zero cyclic sum does not imply zero trace. -/
theorem thirdRoot_trace_eq_neg_one : Matrix.trace thirdRoot = -1 := by
  norm_num [thirdRoot, Matrix.trace, Fin.sum_univ_two]

/-- One member of a real conjugate pair of primitive cubic roots. -/
def cubicLeft : Matrix (Fin 2) (Fin 2) Mat2 :=
  sylvesterBlockMat thirdRoot (thirdRoot ^ 2) 0

/-- A second primitive cubic root with a nonzero upper-right block. -/
def cubicRight : Matrix (Fin 2) (Fin 2) Mat2 :=
  sylvesterBlockMat thirdRoot (thirdRoot ^ 2) 1

/-- The exact direction generating the real unipotent conjugation. -/
def cubicShearDirection : Mat2 :=
  (1 / 3 : ℝ) • (thirdRoot - thirdRoot ^ 2)

/-- These roots are conjugate by the owner's unipotent Sylvester matrix. -/
theorem cubicRight_eq_unipotent_conjugate :
    sylvesterUnipotentG cubicShearDirection * cubicLeft *
      sylvesterUnipotentG (-cubicShearDirection) = cubicRight := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [cubicShearDirection, cubicLeft, cubicRight, sylvesterUnipotentG,
      sylvesterBlockMat, thirdRoot, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The conjugating matrices are two-sided inverses. -/
theorem cubicShear_two_sided_inverse :
    sylvesterUnipotentG cubicShearDirection *
        sylvesterUnipotentG (-cubicShearDirection) = 1 ∧
      sylvesterUnipotentG (-cubicShearDirection) *
        sylvesterUnipotentG cubicShearDirection = 1 := by
  constructor
  · exact (sylvester_operator_matrix_unipotent_diagonalization_and_powers
      (0 : Mat2) 0 cubicShearDirection 0).2.2.2.1
  · simpa using (sylvester_operator_matrix_unipotent_diagonalization_and_powers
      (0 : Mat2) 0 (-cubicShearDirection) 0).2.2.2.1

/-- The first operator satisfies the primitive cubic cyclotomic polynomial. -/
theorem cubicLeft_cyclotomic_three :
    Polynomial.aeval cubicLeft (Polynomial.cyclotomic 3 ℝ) = 0 := by
  rw [Polynomial.cyclotomic_three]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [cubicLeft, sylvesterBlockMat, thirdRoot, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The conjugate operator satisfies the same cyclotomic polynomial. -/
theorem cubicRight_cyclotomic_three :
    Polynomial.aeval cubicRight (Polynomial.cyclotomic 3 ℝ) = 0 := by
  rw [Polynomial.cyclotomic_three]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [cubicRight, sylvesterBlockMat, thirdRoot, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Noncommutativity does not prevent the product from remaining a
primitive cubic cyclotomic root. -/
theorem cubicLeft_mul_cubicRight_cyclotomic_three :
    Polynomial.aeval (cubicLeft * cubicRight) (Polynomial.cyclotomic 3 ℝ) = 0 := by
  rw [Polynomial.cyclotomic_three]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [cubicLeft, cubicRight, sylvesterBlockMat, thirdRoot, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The two conjugate roots genuinely fail to commute. -/
theorem cubicLeft_mul_cubicRight_ne_reverse :
    cubicLeft * cubicRight ≠ cubicRight * cubicLeft := by
  intro h
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) Mat2 => M 0 1 0 1) h
  norm_num [cubicLeft, cubicRight, sylvesterBlockMat, thirdRoot, pow_two,
    Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- A vanishing geometric sum at a nonprimitive fourth root does not
cancel all mixed fourth-order quantum-binomial coefficients. -/
theorem nonprimitive_fourth_root_mixed_coefficient :
    (1 : ℝ) + (-1) + (-1) ^ 2 + (-1) ^ 3 = 0 ∧
      InfoGeometry.Algebra.Quantum.qBinomial (-1 : ℝ) 4 2 = 2 := by
  norm_num [InfoGeometry.Algebra.Quantum.qBinomial]

end InfoGeometry.Algebra.CyclotomicRealCounterexamples
