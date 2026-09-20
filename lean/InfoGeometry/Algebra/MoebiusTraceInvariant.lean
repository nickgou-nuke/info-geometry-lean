import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.MoebiusTraceInvariant

abbrev Mat2 := FiniteSpin.Mat2C

def traceRatio (matrix : Mat2) : ℂ := Matrix.trace matrix ^ 2 / matrix.det

theorem traceRatio_smul (matrix : Mat2) (scalar : ℂ) (hnonzero : scalar ≠ 0) :
    traceRatio (scalar • matrix) = traceRatio matrix := by
  simp only [traceRatio, Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two,
    Matrix.smul_apply, smul_eq_mul]
  have htrace : (scalar * matrix 0 0 + scalar * matrix 1 1) ^ 2 =
      scalar ^ 2 * (matrix 0 0 + matrix 1 1) ^ 2 := by ring
  have hdet : scalar * matrix 0 0 * (scalar * matrix 1 1) -
      scalar * matrix 0 1 * (scalar * matrix 1 0) =
        scalar ^ 2 * (matrix 0 0 * matrix 1 1 - matrix 0 1 * matrix 1 0) := by ring
  change (scalar * matrix 0 0 + scalar * matrix 1 1) ^ 2 /
      (scalar * matrix 0 0 * (scalar * matrix 1 1) -
        scalar * matrix 0 1 * (scalar * matrix 1 0)) =
    (matrix 0 0 + matrix 1 1) ^ 2 /
      (matrix 0 0 * matrix 1 1 - matrix 0 1 * matrix 1 0)
  rw [htrace, hdet, mul_div_mul_left _ _ (pow_ne_zero 2 hnonzero)]

def diagonalRepresentative (parameter : ℂ) : Mat2 :=
  !![parameter, 0; 0, parameter⁻¹]

theorem diagonalRepresentative_det (parameter : ℂ) (hnonzero : parameter ≠ 0) :
    (diagonalRepresentative parameter).det = 1 := by
  simp [diagonalRepresentative, Matrix.det_fin_two, hnonzero]

theorem diagonalRepresentative_traceRatio (parameter : ℂ) (hnonzero : parameter ≠ 0) :
    traceRatio (diagonalRepresentative parameter) = (parameter + parameter⁻¹) ^ 2 := by
  simp [traceRatio, diagonalRepresentative, Matrix.trace, Fin.sum_univ_two]
  field_simp [hnonzero]

theorem complex_example_traceRatio :
    traceRatio (diagonalRepresentative (2 + Complex.I)) =
      128 / 25 + (96 / 25 : ℂ) * Complex.I := by
  have hnonzero : (2 + Complex.I : ℂ) ≠ 0 := by
    intro hequal
    have hreal := congrArg Complex.re hequal
    norm_num at hreal
  have hinverse : (2 + Complex.I : ℂ)⁻¹ = (2 - Complex.I) / 5 := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf <;> norm_num [Complex.I_sq]
  rw [diagonalRepresentative_traceRatio _ hnonzero, hinverse]
  ring_nf

theorem complex_example_nonreal :
    (traceRatio (diagonalRepresentative (2 + Complex.I))).im ≠ 0 := by
  rw [complex_example_traceRatio]
  norm_num

theorem identity_traceRatio : traceRatio (1 : Mat2) = 4 := by
  norm_num [traceRatio, Matrix.trace, Fin.sum_univ_two]

theorem complex_example_discriminant :
    Matrix.trace (diagonalRepresentative (2 + Complex.I)) ^ 2 -
      4 * (diagonalRepresentative (2 + Complex.I)).det =
        28 / 25 + (96 / 25 : ℂ) * Complex.I := by
  have hnonzero : (2 + Complex.I : ℂ) ≠ 0 := by
    intro hequal
    have hreal := congrArg Complex.re hequal
    norm_num at hreal
  have hratio := complex_example_traceRatio
  rw [traceRatio, diagonalRepresentative_det _ hnonzero, div_one] at hratio
  rw [diagonalRepresentative_det _ hnonzero, hratio]
  ring

theorem imaginary_parameter_traceRatio :
    traceRatio (diagonalRepresentative (2 * Complex.I)) = -(9 / 4 : ℂ) := by
  have hnonzero : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hinverse : (2 * Complex.I : ℂ)⁻¹ = -Complex.I / 2 := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf <;> norm_num [Complex.I_sq]
  rw [diagonalRepresentative_traceRatio _ hnonzero, hinverse]
  ring_nf <;> norm_num [Complex.I_sq]

end InfoGeometry.Algebra.MoebiusTraceInvariant
