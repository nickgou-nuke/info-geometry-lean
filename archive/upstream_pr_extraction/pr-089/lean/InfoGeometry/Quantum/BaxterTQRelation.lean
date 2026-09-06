import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BaxterTQRelation

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def baxterQFunction (Γ u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def baxterQShiftForward (Γ u η : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def baxterQShiftBackward (Γ u η : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def baxterTransferEigenvalue (Γ η : ℝ) : ℂ :=
  ((2 * Real.cosh ((Γ / 2) * η) : ℝ) : ℂ)

theorem baxter_Q_shift_forward_eq (Γ u η : ℝ) :
    baxterQShiftForward Γ u η =
    ((Real.exp (- (Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u := by
  unfold baxterQShiftForward baxterQFunction
  have h_add : Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) =
               - (((Γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) := by
    have h_I : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ))
      _ = Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) + (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) := by ring
      _ = Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) + (-1) * (((Γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
      _ = - (((Γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) := by ring
  rw [h_add, Complex.exp_add]
  have h_exp : Complex.exp (- (((Γ / 2 * η : ℝ) : ℂ))) = ((Real.exp (- (Γ / 2 * η)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_exp]

theorem baxter_Q_shift_backward_eq (Γ u η : ℝ) :
    baxterQShiftBackward Γ u η =
    ((Real.exp ((Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u := by
  unfold baxterQShiftBackward baxterQFunction
  have h_add : Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) =
               (((Γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) := by
    have h_I : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ))
      _ = Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) - (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) := by ring
      _ = Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) - (-1) * (((Γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
      _ = (((Γ / 2 * η : ℝ) : ℂ)) + Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) := by ring
  rw [h_add, Complex.exp_add]
  have h_exp : Complex.exp (((Γ / 2 * η : ℝ) : ℂ)) = ((Real.exp ((Γ / 2 * η)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_exp]

theorem baxter_TQ_exact_relation (Γ u η : ℝ) :
    baxterTransferEigenvalue Γ η * baxterQFunction Γ u =
    baxterQShiftForward Γ u η + baxterQShiftBackward Γ u η := by
  rw [baxter_Q_shift_forward_eq, baxter_Q_shift_backward_eq]
  unfold baxterTransferEigenvalue
  have h_cosh_def : Real.exp (- (Γ / 2 * η)) + Real.exp (Γ / 2 * η) = 2 * Real.cosh ((Γ / 2) * η) := by
    have h_cosh := Real.cosh_eq ((Γ / 2) * η)
    have : (Γ / 2 * η) = (Γ / 2) * η := by ring
    rw [this]
    linarith
  have h_sum : ((Real.exp (- (Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u +
               ((Real.exp (Γ / 2 * η) : ℝ) : ℂ) * baxterQFunction Γ u =
               (((Real.exp (- (Γ / 2 * η)) + Real.exp (Γ / 2 * η) : ℝ) : ℂ)) * baxterQFunction Γ u := by
    push_cast
    ring
  rw [h_sum, h_cosh_def]

theorem baxter_Q_unitary (Γ u : ℝ) :
    ‖baxterQFunction Γ u‖ = 1 := by
  unfold baxterQFunction
  have h_re : (Complex.I * (((Γ / 2 * u : ℝ) : ℂ))).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_abs := Complex.norm_exp (Complex.I * (((Γ / 2 * u : ℝ) : ℂ)))
  rw [h_re, Real.exp_zero] at h_abs
  exact h_abs

theorem grand_baxter_TQ_synthesis (Γ u η : ℝ) :
    (baxterQShiftForward Γ u η = ((Real.exp (- (Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u) ∧
    (baxterQShiftBackward Γ u η = ((Real.exp ((Γ / 2 * η)) : ℝ) : ℂ) * baxterQFunction Γ u) ∧
    (‖baxterQFunction Γ u‖ = 1) ∧
    (baxterTransferEigenvalue Γ η * baxterQFunction Γ u =
     baxterQShiftForward Γ u η + baxterQShiftBackward Γ u η) :=
  ⟨baxter_Q_shift_forward_eq Γ u η,
   baxter_Q_shift_backward_eq Γ u η,
   baxter_Q_unitary Γ u,
   baxter_TQ_exact_relation Γ u η⟩
