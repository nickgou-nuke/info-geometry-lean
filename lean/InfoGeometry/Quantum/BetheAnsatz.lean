import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BetheAnsatz

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def vacuumEigenvalueA (Γ u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def vacuumEigenvalueD (Γ u : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def betheVacuumRatio (Γ u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Γ * u : ℝ) : ℂ))

def betheScatteringPhase (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (θ : ℂ))

theorem vacuum_eigenvalues_unitary (Γ u : ℝ) :
    ‖vacuumEigenvalueA Γ u‖ = 1 ∧
    ‖vacuumEigenvalueD Γ u‖ = 1 := by
  unfold vacuumEigenvalueA vacuumEigenvalueD
  have h_re_A : (Complex.I * (((Γ / 2 * u : ℝ) : ℂ))).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_re_D : (-Complex.I * (((Γ / 2 * u : ℝ) : ℂ))).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_abs_A := Complex.norm_exp (Complex.I * (((Γ / 2 * u : ℝ) : ℂ)))
  have h_abs_D := Complex.norm_exp (-Complex.I * (((Γ / 2 * u : ℝ) : ℂ)))
  rw [h_re_A, Real.exp_zero] at h_abs_A
  rw [h_re_D, Real.exp_zero] at h_abs_D
  exact ⟨h_abs_A, h_abs_D⟩

theorem bethe_vacuum_ratio_exact (Γ u : ℝ) :
    vacuumEigenvalueA Γ u / vacuumEigenvalueD Γ u = betheVacuumRatio Γ u := by
  unfold vacuumEigenvalueA vacuumEigenvalueD betheVacuumRatio
  rw [← Complex.exp_sub]
  have : Complex.I * (((Γ / 2) * u : ℝ) : ℂ) - -Complex.I * (((Γ / 2) * u : ℝ) : ℂ) =
         Complex.I * ((Γ * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this]

theorem vacuum_transfer_eigenvalue (Γ u : ℝ) :
    vacuumEigenvalueA Γ u + vacuumEigenvalueD Γ u = ((2 * Real.cos ((Γ / 2) * u) : ℝ) : ℂ) := by
  unfold vacuumEigenvalueA vacuumEigenvalueD
  have h1 : Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ)) =
            Complex.cos (((Γ / 2) * u : ℝ) : ℂ) + Complex.sin (((Γ / 2) * u : ℝ) : ℂ) * Complex.I := by
    have h := Complex.exp_mul_I (((Γ / 2) * u : ℝ) : ℂ)
    have hc : (((Γ / 2) * u : ℝ) : ℂ) * Complex.I = Complex.I * (((Γ / 2) * u : ℝ) : ℂ) := mul_comm _ _
    rwa [hc] at h
  have h2 : Complex.exp (-Complex.I * (((Γ / 2) * u : ℝ) : ℂ)) =
            Complex.cos (- (((Γ / 2) * u : ℝ) : ℂ)) + Complex.sin (- (((Γ / 2) * u : ℝ) : ℂ)) * Complex.I := by
    have h_neg : -Complex.I * (((Γ / 2) * u : ℝ) : ℂ) = (- (((Γ / 2) * u : ℝ) : ℂ)) * Complex.I := by ring
    rw [h_neg]
    exact Complex.exp_mul_I (- (((Γ / 2) * u : ℝ) : ℂ))
  rw [h1, h2, Complex.cos_neg, Complex.sin_neg]
  have h_cos : Complex.cos (((Γ / 2) * u : ℝ) : ℂ) = ((Real.cos ((Γ / 2) * u) : ℝ) : ℂ) :=
    (Complex.ofReal_cos ((Γ / 2) * u)).symm
  rw [h_cos]
  push_cast
  ring

theorem bethe_ansatz_root_condition (Γ u_k Θ : ℝ) :
    betheVacuumRatio Γ u_k = betheScatteringPhase Θ ↔
    Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) = 1 := by
  unfold betheVacuumRatio betheScatteringPhase
  constructor
  · intro h
    have h_div : Complex.exp (Complex.I * ((Γ * u_k : ℝ) : ℂ)) /
                 Complex.exp (Complex.I * (Θ : ℂ)) = 1 := by
      rw [h, div_self (Complex.exp_ne_zero _)]
    have h_sub_exp : Complex.exp (Complex.I * ((Γ * u_k : ℝ) : ℂ)) /
                     Complex.exp (Complex.I * (Θ : ℂ)) =
                     Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) := by
      rw [← Complex.exp_sub]
      have : Complex.I * ((Γ * u_k : ℝ) : ℂ) - Complex.I * (Θ : ℂ) =
             Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [this]
    rwa [← h_sub_exp]
  · intro h
    have h_mul : Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) *
                 Complex.exp (Complex.I * (Θ : ℂ)) =
                 Complex.exp (Complex.I * (Θ : ℂ)) := by
      rw [h, one_mul]
    have h_add_exp : Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) *
                     Complex.exp (Complex.I * (Θ : ℂ)) =
                     Complex.exp (Complex.I * ((Γ * u_k : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      have : Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ)) + Complex.I * (Θ : ℂ) =
             Complex.I * ((Γ * u_k : ℝ) : ℂ) := by
        push_cast
        ring
      rw [this]
    rwa [← h_add_exp]

theorem bethe_logarithmic_quantization (Γ u_k Θ : ℝ) (I_k : ℤ)
    (h_quant : Γ * u_k - Θ = 2 * Real.pi * (I_k : ℝ)) :
    Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) = 1 := by
  rw [h_quant]
  push_cast
  have h_comm : Complex.I * (2 * Real.pi * (I_k : ℂ)) = (I_k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h_comm]
  exact Complex.exp_int_mul_two_pi_mul_I I_k
