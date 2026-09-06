import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BaxterQQWronskian

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def baxterQPos (Γ u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def baxterQNeg (Γ u : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (((Γ / 2) * u : ℝ) : ℂ))

def baxterQPosShiftForward (Γ u η : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def baxterQPosShiftBackward (Γ u η : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def baxterQNegShiftForward (Γ u η : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def baxterQNegShiftBackward (Γ u η : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)))

def quantumWronskian (Γ u η : ℝ) : ℂ :=
  baxterQPosShiftForward Γ u η * baxterQNegShiftBackward Γ u η -
  baxterQPosShiftBackward Γ u η * baxterQNegShiftForward Γ u η

def wronskianConstant (Γ η : ℝ) : ℂ :=
  - ((2 * Real.sinh (Γ * η) : ℝ) : ℂ)

theorem baxter_Q_pos_mul_neg_eq_one (Γ u : ℝ) :
    baxterQPos Γ u * baxterQNeg Γ u = 1 := by
  unfold baxterQPos baxterQNeg
  rw [← Complex.exp_add]
  have : Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) + -Complex.I * (((Γ / 2 * u : ℝ) : ℂ)) = 0 := by ring
  rw [this, Complex.exp_zero]

theorem quantum_wronskian_eq_constant (Γ u η : ℝ) :
    quantumWronskian Γ u η = wronskianConstant Γ η := by
  unfold quantumWronskian wronskianConstant baxterQPosShiftForward baxterQNegShiftBackward baxterQPosShiftBackward baxterQNegShiftForward
  rw [← Complex.exp_add, ← Complex.exp_add]
  have h_I : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h1 : Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) +
            -Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) =
            - (((Γ * η : ℝ) : ℂ)) := by
    calc Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) +
         -Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ))
      _ = (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) + (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) := by ring
      _ = (-1) * (((Γ / 2 * η : ℝ) : ℂ)) + (-1) * (((Γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
      _ = - (((Γ * η : ℝ) : ℂ)) := by
        push_cast
        ring
  have h2 : Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) +
            -Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) =
            (((Γ * η : ℝ) : ℂ)) := by
    calc Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) - Complex.I * (((Γ / 2) * η : ℝ) : ℂ)) +
         -Complex.I * ((((Γ / 2) * u : ℝ) : ℂ) + Complex.I * (((Γ / 2) * η : ℝ) : ℂ))
      _ = - (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) - (Complex.I * Complex.I) * (((Γ / 2 * η : ℝ) : ℂ)) := by ring
      _ = - (-1) * (((Γ / 2 * η : ℝ) : ℂ)) - (-1) * (((Γ / 2 * η : ℝ) : ℂ)) := by rw [h_I]
      _ = (((Γ * η : ℝ) : ℂ)) := by
        push_cast
        ring
  rw [h1, h2]
  have h_exp1 : Complex.exp (- (((Γ * η : ℝ) : ℂ))) = ((Real.exp (- (Γ * η)) : ℝ) : ℂ) := by
    push_cast
    rfl
  have h_exp2 : Complex.exp (((Γ * η : ℝ) : ℂ)) = ((Real.exp ((Γ * η)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_exp1, h_exp2]
  have h_sinh_def : Real.exp (- (Γ * η)) - Real.exp (Γ * η) = - (2 * Real.sinh (Γ * η)) := by
    have h_sinh := Real.sinh_eq (Γ * η)
    linarith
  have h_push : ((Real.exp (- (Γ * η)) : ℝ) : ℂ) - ((Real.exp (Γ * η) : ℝ) : ℂ) =
                (((Real.exp (- (Γ * η)) - Real.exp (Γ * η) : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [h_push, h_sinh_def]
  push_cast
  rfl

theorem hasDerivAt_wronskian_zero (Γ η : ℝ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => wronskianConstant Γ η) 0 u :=
  hasDerivAt_const u (wronskianConstant Γ η)

theorem grand_quantum_wronskian_synthesis (Γ u η : ℝ) :
    (baxterQPos Γ u * baxterQNeg Γ u = 1) ∧
    (quantumWronskian Γ u η = wronskianConstant Γ η) ∧
    (HasDerivAt (fun x : ℝ => wronskianConstant Γ η) 0 u) :=
  ⟨baxter_Q_pos_mul_neg_eq_one Γ u,
   quantum_wronskian_eq_constant Γ u η,
   hasDerivAt_wronskian_zero Γ η u⟩
