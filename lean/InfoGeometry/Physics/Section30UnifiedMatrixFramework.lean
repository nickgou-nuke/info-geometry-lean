import Mathlib
import InfoGeometryCore.Basic

open InfoGeometryCore
/-!
# Section 30 repaired: finite Pauli/Bloch/Minkowski matrix framework

The source `section30.txt` contains a useful finite matrix core but also several
unsupported claims.  This file repairs the mathematics by proving only the
finite algebraic statements that follow directly from `2 × 2` matrices.

Repairs/guardrails:

* the quaternion embedding sign is corrected: with `i ↦ I σ₁` and
  `j ↦ I σ₂`, one has `(I σ₁)(I σ₂) = - I σ₃`; therefore the compatible
  image of quaternion `k` is `-I σ₃`, not `+I σ₃`;
* the Hermitian/Minkowski determinant identity is proved for the unnormalized
  matrix `t I + x σ₁ + y σ₂ + z σ₃` to avoid irrelevant square-root bookkeeping;
* Bloch trace and determinant identities are proved exactly;
* no Bloch-sphere/Riemann-sphere diffeomorphism, Einstein-equation derivation,
  gravity-from-entanglement theorem, or spacetime-emergence theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Physics.Section30UnifiedMatrixFramework

open Matrix Complex

/-- Complex `2 × 2` matrices. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- First Pauli matrix. -/
abbrev sigma1 := sigma1C

/-- Second Pauli matrix. -/
abbrev sigma2 := sigma2C

/-- Third Pauli matrix. -/
abbrev sigma3 := sigma3C

/-- `σ₁² = I`. -/
theorem sigma1_sq : sigma1 * sigma1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma1C, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ₂² = I`. -/
theorem sigma2_sq : sigma2 * sigma2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma2, sigma2C, Matrix.mul_apply, Fin.sum_univ_two]

/-- `σ₃² = I`. -/
theorem sigma3_sq : sigma3 * sigma3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma3, sigma3C, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli multiplication: `σ₁ σ₂ = I σ₃`. -/
theorem sigma1_mul_sigma2 : sigma1 * sigma2 = Complex.I • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Pauli multiplication: `σ₂ σ₃ = I σ₁`. -/
theorem sigma2_mul_sigma3 : sigma2 * sigma3 = Complex.I • sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Pauli multiplication: `σ₃ σ₁ = I σ₂`. -/
theorem sigma3_mul_sigma1 : sigma3 * sigma1 = Complex.I • sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Corrected quaternion-image basis element corresponding to quaternion `i`. -/
def quatI : Mat2C := Complex.I • sigma1

/-- Corrected quaternion-image basis element corresponding to quaternion `j`. -/
def quatJ : Mat2C := Complex.I • sigma2

/-- Corrected quaternion-image basis element corresponding to quaternion `k`. -/
def quatK : Mat2C := -(Complex.I • sigma3)

/-- The corrected image has `i² = -1`. -/
theorem quatI_sq : quatI * quatI = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, sigma1, sigma1C, Matrix.mul_apply, Fin.sum_univ_two]

/-- The corrected image has `j² = -1`. -/
theorem quatJ_sq : quatJ * quatJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatJ, sigma2, sigma2C, Matrix.mul_apply, Fin.sum_univ_two]

/-- The corrected image has `k² = -1`. -/
theorem quatK_sq : quatK * quatK = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatK, sigma3, sigma3C, Matrix.mul_apply, Fin.sum_univ_two]

/-- Corrected quaternion sign: `(Iσ₁)(Iσ₂) = -Iσ₃`, i.e. `ij = k`. -/
theorem quatI_mul_quatJ : quatI * quatJ = quatK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatI, quatJ, quatK, sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Unnormalized Hermitian/Minkowski matrix `t I + x σ₁ + y σ₂ + z σ₃`. -/
def spacetimeMatrix (t x y z : ℝ) : Mat2C :=
  ((t : ℂ) • (1 : Mat2C)) + ((x : ℂ) • sigma1) +
    ((y : ℂ) • sigma2) + ((z : ℂ) • sigma3)

/-- Minkowski quadratic form with signature `(-,+,+,+)`. -/
def minkowskiForm (t x y z : ℝ) : ℂ :=
  -(t : ℂ) ^ 2 + (x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2

/-- Determinant of the unnormalized Pauli spacetime matrix. -/
theorem spacetimeMatrix_det (t x y z : ℝ) :
    (spacetimeMatrix t x y z).det =
      (t : ℂ) ^ 2 - (x : ℂ) ^ 2 - (y : ℂ) ^ 2 - (z : ℂ) ^ 2 := by
  simp [spacetimeMatrix, sigma1, sigma2, sigma3, Matrix.det_fin_two]
  simp [sigma1C, sigma2C, sigma3C]
  ring_nf
  rw [pow_two (Complex.I : ℂ), Complex.I_mul_I]
  ring

/-- The determinant identity is equivalently `-det =` the Minkowski form. -/
theorem neg_det_spacetimeMatrix_eq_minkowskiForm (t x y z : ℝ) :
    - (spacetimeMatrix t x y z).det = minkowskiForm t x y z := by
  rw [spacetimeMatrix_det]
  unfold minkowskiForm
  ring

/-- Bloch density matrix `ρ = 1/2 (I + n·σ)`. -/
def blochMatrix (nx ny nz : ℝ) : Mat2C :=
  (1 / 2 : ℂ) •
    ((1 : Mat2C) + ((nx : ℂ) • sigma1) + ((ny : ℂ) • sigma2) + ((nz : ℂ) • sigma3))

/-- Every finite Bloch matrix has trace one. -/
theorem blochMatrix_trace (nx ny nz : ℝ) :
    (blochMatrix nx ny nz).trace = 1 := by
  simp [blochMatrix, sigma1, sigma2, sigma3, sigma1C, sigma2C, sigma3C, Matrix.trace,
    Fin.sum_univ_two]
  ring_nf

/-- Determinant of the finite Bloch matrix. -/
theorem blochMatrix_det (nx ny nz : ℝ) :
    (blochMatrix nx ny nz).det =
      ((1 : ℂ) - (nx : ℂ) ^ 2 - (ny : ℂ) ^ 2 - (nz : ℂ) ^ 2) / 4 := by
  simp [blochMatrix, sigma1, sigma2, sigma3, Matrix.det_fin_two]
  simp [sigma1C, sigma2C, sigma3C]
  ring_nf
  rw [pow_two (Complex.I : ℂ), Complex.I_mul_I]
  ring

/-- If the Bloch vector has unit Euclidean norm, the Bloch determinant is zero. -/
theorem blochMatrix_det_eq_zero_of_unit_norm {nx ny nz : ℝ}
    (h : nx ^ 2 + ny ^ 2 + nz ^ 2 = 1) :
    (blochMatrix nx ny nz).det = 0 := by
  rw [blochMatrix_det]
  have hr : (1 : ℝ) - nx ^ 2 - ny ^ 2 - nz ^ 2 = 0 := by nlinarith
  have hc : (1 : ℂ) - (nx : ℂ)^2 - (ny : ℂ)^2 - (nz : ℂ)^2 = 0 := by
    norm_num [← Complex.ofReal_pow]
    exact_mod_cast hr
  rw [hc]
  norm_num

/-- Repaired finite Section 30 packet: determinant and Bloch trace identities. -/
theorem repaired_section30_matrix_packet (t x y z nx ny nz : ℝ) :
    - (spacetimeMatrix t x y z).det = minkowskiForm t x y z ∧
      (blochMatrix nx ny nz).trace = 1 := by
  exact ⟨neg_det_spacetimeMatrix_eq_minkowskiForm t x y z,
    blochMatrix_trace nx ny nz⟩

end InfoGeometry.Physics.Section30UnifiedMatrixFramework

end noncomputable section
