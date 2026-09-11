import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.TransferMatrixIntegrability

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def laxPhaseFactor (Γ u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def quantumTransferMatrix (Γ u : ℝ) : ℂ :=
  laxPhaseFactor Γ u + laxPhaseFactor (-Γ) u

def quantumTransferMatrixReal (Γ u : ℝ) : ℝ :=
  2 * Real.cos ((Γ / 2) * u)

theorem transfer_matrix_eq_two_cos (Γ u : ℝ) :
    quantumTransferMatrix Γ u = ((quantumTransferMatrixReal Γ u : ℝ) : ℂ) := by
  unfold quantumTransferMatrix quantumTransferMatrixReal laxPhaseFactor
  have h1 : Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ)) =
            Complex.cos (((Γ / 2) * u : ℝ) : ℂ) + Complex.sin (((Γ / 2) * u : ℝ) : ℂ) * Complex.I := by
    have h := Complex.exp_mul_I (((Γ / 2) * u : ℝ) : ℂ)
    have hc : (((Γ / 2) * u : ℝ) : ℂ) * Complex.I = Complex.I * (((Γ / 2) * u : ℝ) : ℂ) := mul_comm _ _
    rwa [hc] at h
  have h_neg_cast : (((-Γ / 2) * u : ℝ) : ℂ) = - (((Γ / 2) * u : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * (((-Γ / 2) * u : ℝ) : ℂ)) =
            Complex.cos (- (((Γ / 2) * u : ℝ) : ℂ)) + Complex.sin (- (((Γ / 2) * u : ℝ) : ℂ)) * Complex.I := by
    rw [h_neg_cast]
    have h := Complex.exp_mul_I (- (((Γ / 2) * u : ℝ) : ℂ))
    have hc : (- (((Γ / 2) * u : ℝ) : ℂ)) * Complex.I = Complex.I * (- (((Γ / 2) * u : ℝ) : ℂ)) := mul_comm _ _
    rwa [hc] at h
  rw [h1, h2, Complex.cos_neg, Complex.sin_neg]
  have h_cos : Complex.cos (((Γ / 2) * u : ℝ) : ℂ) = ((Real.cos ((Γ / 2) * u) : ℝ) : ℂ) :=
    (Complex.ofReal_cos ((Γ / 2) * u)).symm
  rw [h_cos]
  push_cast
  ring

theorem transfer_matrix_at_zero (Γ : ℝ) :
    quantumTransferMatrixReal Γ 0 = 2 := by
  unfold quantumTransferMatrixReal
  have h_zero : (Γ / 2) * 0 = 0 := mul_zero (Γ / 2)
  rw [h_zero, Real.cos_zero, mul_one]

theorem transfer_matrix_even_u (Γ u : ℝ) :
    quantumTransferMatrixReal Γ (-u) = quantumTransferMatrixReal Γ u := by
  unfold quantumTransferMatrixReal
  have h_neg : (Γ / 2) * (-u) = - ((Γ / 2) * u) := by ring
  rw [h_neg, Real.cos_neg]

theorem transfer_matrix_even_gamma (Γ u : ℝ) :
    quantumTransferMatrixReal (-Γ) u = quantumTransferMatrixReal Γ u := by
  unfold quantumTransferMatrixReal
  have h_neg : (-Γ / 2) * u = - ((Γ / 2) * u) := by ring
  rw [h_neg, Real.cos_neg]

theorem transfer_matrix_commutation (Γ u v : ℝ) :
    quantumTransferMatrix Γ u * quantumTransferMatrix Γ v -
    quantumTransferMatrix Γ v * quantumTransferMatrix Γ u = 0 := by
  ring

theorem lax_phase_additive (Γ₁ Γ₂ u : ℝ) :
    laxPhaseFactor (Γ₁ + Γ₂) u = laxPhaseFactor Γ₁ u * laxPhaseFactor Γ₂ u := by
  unfold laxPhaseFactor
  have h_distrib : (((Γ₁ + Γ₂) / 2) * u : ℝ) = ((Γ₁ / 2) * u : ℝ) + ((Γ₂ / 2) * u : ℝ) := by ring
  rw [h_distrib]
  push_cast
  have h_add : Complex.I * (↑Γ₁ / 2 * ↑u + ↑Γ₂ / 2 * ↑u) =
               Complex.I * (↑Γ₁ / 2 * ↑u) + Complex.I * (↑Γ₂ / 2 * ↑u) := by ring
  rw [h_add, Complex.exp_add]

end
end InfoGeometry.Quantum.TransferMatrixIntegrability
