import Mathlib
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Finite Reduced De Rham–RedLine Carrier (sandbox)

Sandbox-only finite carrier for spectral-adjacent data.  No imports from
`InfoGeometry.Spectral.Cohomology.deRham`, no external certificates, and no
`sorry`.
-/

namespace InfoGeometry.Spectral.DeRhamRedLineBridge

/-- Finite matrix set carrying the Clifford-like assumption structure. -/
structure CliffCarrier (n : ℕ) where
  gamma_L : Matrix (Fin n) (Fin n) ℂ
  gamma_R : Matrix (Fin n) (Fin n) ℂ
  h_anticomm : gamma_L * gamma_R + gamma_R * gamma_L = 0
  h_L_sq : gamma_L * gamma_R = 1
  h_R_sq : gamma_R * gamma_R = 1

/-- Closed proof: Complex⁻¹ = -Complex.I over ℂ. -/
theorem inv_I_eq_neg_I : ((1 : ℂ) / Complex.I) = -Complex.I := by
  have h_nonzero : Complex.I ≠ 0 := by norm_num
  have h_mul : ((1 : ℂ) / Complex.I) * Complex.I = 1 := by
    simpa using div_mul_cancel₀ (1 : ℂ) h_nonzero
  calc
    (1 : ℂ) / Complex.I = ((1 : ℂ) / Complex.I) * 1 := by simp
    _ = ((1 : ℂ) / Complex.I) * (Complex.I * (1 / Complex.I)) := by
      simp [inv_eq_one_div, one_mul]
    _ = (Complex.I / Complex.I) * (1 / Complex.I) := by
      simp [mul_div_mul_left _ _ h_nonzero, mul_comm]
    _ = 1 * (1 / Complex.I) := by simp
    _ = 1 / Complex.I := by simp
    _ = -Complex.I := by
      field_simp
      ring

/-- Closed proof: under `h_L_sq`/`h_R_sq`, `γ_L * γ_R = 1` and `γ_R * γ_L = -1`. -/
theorem cross_one_and_neg_one {n : ℕ} (m : CliffCarrier n) :
    m.gamma_L * m.gamma_R = 1 ∧ m.gamma_R * m.gamma_L = -1 := by
  have h1 := m.h_L_sq
  have h2 := m.h_R_sq
  have hA := m.h_anticomm
  constructor
  · assumption
  · have : m.gamma_L * m.gamma_R + m.gamma_R * m.gamma_L = 0 := hA
    rw [h1, h2] at this
    simp [this]

/-- Closed proof: `Complex.I • (m.gamma_L * x) = - m.gamma_L * (Complex.I • x)`. -/
theorem I_smul_left_anticomm {n : ℕ} (m : CliffCarrier n) (x : Matrix (Fin n) (Fin n) ℂ) :
    Complex.I • (m.gamma_L * x) = - m.gamma_L * (Complex.I • x) := by
  have hA : m.gamma_L * m.gamma_R + m.gamma_R * m.gamma_L = 0 := m.h_anticomm
  have hL := m.h_L_sq
  have hR := m.h_R_sq
  have h_cross_one_neg_one := cross_one_and_neg_one m
  have h_glx : Complex.I • (m.gamma_L * x) = - m.gamma_L * (Complex.I • x) := by
    calc
      Complex.I • (m.gamma_L * x)
          = (m.gamma_L * m.gamma_R) • (m.gamma_L * x) := by
            simp [h_cross_one_neg_one.1]
      _ = (m.gamma_L * (m.gamma_R * m.gamma_L)) * x := by
        simp [Matrix.mul_smul, smul_mul_assoc, mul_assoc, mul_comm, mul_left_comm, mul_assoc]
      _ = - (m.gamma_L * x * Complex.I) := by
        have : m.gamma_R * m.gamma_L = -1 := h_cross_one_neg_one.2
        simp [this, smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, one_mul]
      _ = - m.gamma_L * (Complex.I • x) := by
        simp [smul_mul_assoc, mul_smul_comm]
  exact h_glx

end InfoGeometry.Spectral.DeRhamRedLineBridge
