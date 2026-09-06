import InfoGeometry.Clifford.Cl3ComplexMatrixProduct

/-!
# Gull-Doran-Lasenby pseudoscalar bridge, finite owner surface

This module records the finite matrix corridor behind the geometric-algebra
reading of the scalar imaginary unit:

* the Pauli generators square to `1`;
* the Pauli generators anticommute;
* their `Cl(3)` volume product is the scalar complex phase `I`;
* the same phase has a concrete real `4 × 4` realification squaring to `-1`.

#### BUCKET 1: CLOSED FINITE THEOREMS
All theorem statements below are concrete matrix identities over `ℂ` or `ℝ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
No claim is made about Maxwell equations, Dirac spinors, spacetime-algebra
field theory, continuum geometry, or any Riemann Hypothesis consequence.
-/

namespace InfoGeometry.Clifford.GullDoranPseudoscalarBridge

open scoped Matrix
open InfoGeometry.Clifford.Cl3ComplexMatrixProduct

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-- Concrete real `4 × 4` carrier for the realification of `Mat₂(ℂ)`. -/
abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ

/-- Realification of complex multiplication by `I` on two complex coordinates. -/
def realPhaseAxis : Mat4R :=
  !![(0 : ℝ), -1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 1, 0]

/-- Realification of the first Pauli generator. -/
def realSigma1 : Mat4R :=
  !![(0 : ℝ), 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- Realification of the second Pauli generator. -/
def realSigma2 : Mat4R :=
  !![(0 : ℝ), 0, 0, 1;
     0, 0, -1, 0;
     0, -1, 0, 0;
     1, 0, 0, 0]

/-- Realification of the third Pauli generator. -/
def realSigma3 : Mat4R :=
  !![(1 : ℝ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

theorem pauli_sigma1_sq :
    s1 * s1 = (1 : Mat2C) :=
  s1_sq

theorem pauli_sigma2_sq :
    s2 * s2 = (1 : Mat2C) :=
  s2_sq

theorem pauli_sigma3_sq :
    s3 * s3 = (1 : Mat2C) :=
  s3_sq

theorem pauli_sigma1_sigma2_anticomm :
    s1 * s2 + s2 * s1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s1, s2, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_sigma1_sigma3_anticomm :
    s1 * s3 + s3 * s1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s1, s3, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_sigma2_sigma3_anticomm :
    s2 * s3 + s3 * s2 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s2, s3, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite Pauli volume element is the scalar complex phase. -/
theorem pauli_pseudoscalar_eq_complex_phase :
    s1 * s2 * s3 = Complex.I • (1 : Mat2C) :=
  s1_mul_s2_mul_s3

/-- The Pauli pseudoscalar squares to `-1`. -/
theorem pauli_pseudoscalar_sq :
    (s1 * s2 * s3) * (s1 * s2 * s3) = -(1 : Mat2C) := by
  rw [pauli_pseudoscalar_eq_complex_phase]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

theorem realPhaseAxis_sq :
    realPhaseAxis * realPhaseAxis = -(1 : Mat4R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma1_sq :
    realSigma1 * realSigma1 = (1 : Mat4R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma2_sq :
    realSigma2 * realSigma2 = (1 : Mat4R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma3_sq :
    realSigma3 * realSigma3 = (1 : Mat4R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma1_realSigma2_anticomm :
    realSigma1 * realSigma2 + realSigma2 * realSigma1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma1, realSigma2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma1_realSigma3_anticomm :
    realSigma1 * realSigma3 + realSigma3 * realSigma1 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma1, realSigma3, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realSigma2_realSigma3_anticomm :
    realSigma2 * realSigma3 + realSigma3 * realSigma2 = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma2, realSigma3, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The realified Pauli volume product is the real phase axis. -/
theorem real_pseudoscalar_eq_phaseAxis :
    realSigma1 * realSigma2 * realSigma3 = realPhaseAxis := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realSigma1, realSigma2, realSigma3, realPhaseAxis,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- The realified Pauli volume element squares to `-1`. -/
theorem real_pseudoscalar_sq :
    (realSigma1 * realSigma2 * realSigma3) *
      (realSigma1 * realSigma2 * realSigma3) = -(1 : Mat4R) := by
  rw [real_pseudoscalar_eq_phaseAxis, realPhaseAxis_sq]

/-! The odd-dimensional volume element is central in this concrete real carrier. -/
theorem realPhaseAxis_comm_realSigma1 :
    realPhaseAxis * realSigma1 = realSigma1 * realPhaseAxis := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma1, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realPhaseAxis_comm_realSigma2 :
    realPhaseAxis * realSigma2 = realSigma2 * realPhaseAxis := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma2, Matrix.mul_apply, Fin.sum_univ_succ]

theorem realPhaseAxis_comm_realSigma3 :
    realPhaseAxis * realSigma3 = realSigma3 * realPhaseAxis := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [realPhaseAxis, realSigma3, Matrix.mul_apply, Fin.sum_univ_succ]

/--
Finite capstone: the Pauli `Cl(3)` pseudoscalar is a square-minus-one phase,
and its realification is a concrete real `4 × 4` square-minus-one matrix.
-/
theorem gull_doran_pseudoscalar_capstone :
    s1 * s1 = (1 : Mat2C) ∧
    s2 * s2 = (1 : Mat2C) ∧
    s3 * s3 = (1 : Mat2C) ∧
    s1 * s2 + s2 * s1 = 0 ∧
    s1 * s3 + s3 * s1 = 0 ∧
    s2 * s3 + s3 * s2 = 0 ∧
    s1 * s2 * s3 = Complex.I • (1 : Mat2C) ∧
    (s1 * s2 * s3) * (s1 * s2 * s3) = -(1 : Mat2C) ∧
    realSigma1 * realSigma2 * realSigma3 = realPhaseAxis ∧
    realPhaseAxis * realPhaseAxis = -(1 : Mat4R) ∧
    realPhaseAxis * realSigma1 = realSigma1 * realPhaseAxis ∧
    realPhaseAxis * realSigma2 = realSigma2 * realPhaseAxis ∧
    realPhaseAxis * realSigma3 = realSigma3 * realPhaseAxis :=
  ⟨pauli_sigma1_sq, pauli_sigma2_sq, pauli_sigma3_sq,
    pauli_sigma1_sigma2_anticomm, pauli_sigma1_sigma3_anticomm,
    pauli_sigma2_sigma3_anticomm, pauli_pseudoscalar_eq_complex_phase,
    pauli_pseudoscalar_sq, real_pseudoscalar_eq_phaseAxis, realPhaseAxis_sq,
    realPhaseAxis_comm_realSigma1, realPhaseAxis_comm_realSigma2,
    realPhaseAxis_comm_realSigma3⟩

end InfoGeometry.Clifford.GullDoranPseudoscalarBridge
