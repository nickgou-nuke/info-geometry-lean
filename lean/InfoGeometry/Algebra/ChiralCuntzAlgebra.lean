import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Algebra.ChiralCuntzAlgebra

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def chiralShiftGenerator (N_L N_R : ℝ) : ℝ :=
  (1 / 2) * (N_L - N_R)

def chiralTiltGenerator (N_L N_R : ℝ) : ℝ :=
  (1 / 2) * (N_L + N_R)

def chiralShiftOperator (θ N_L N_R : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((θ * (N_L - N_R) : ℝ) : ℂ))

def chiralTiltOperator (ξ N_L N_R : ℝ) : ℝ :=
  Real.exp (ξ * (N_L + N_R))

def leftNullHop (N_L N_R : ℝ) : ℝ :=
  chiralTiltGenerator N_L N_R + chiralShiftGenerator N_L N_R

def rightNullHop (N_L N_R : ℝ) : ℝ :=
  chiralTiltGenerator N_L N_R - chiralShiftGenerator N_L N_R

def bostConnesKMSOperator (p : ℕ) (N_p : ℝ) (β : ℝ) : ℝ :=
  Real.exp (-β * Real.log (p : ℝ) * N_p)

theorem left_null_hop_eq_N_L (N_L N_R : ℝ) :
    leftNullHop N_L N_R = N_L := by
  unfold leftNullHop chiralTiltGenerator chiralShiftGenerator
  ring

theorem right_null_hop_eq_N_R (N_L N_R : ℝ) :
    rightNullHop N_L N_R = N_R := by
  unfold rightNullHop chiralTiltGenerator chiralShiftGenerator
  ring

theorem shift_generator_diff (N_L N_R : ℝ) :
    2 * chiralShiftGenerator N_L N_R = N_L - N_R := by
  unfold chiralShiftGenerator
  ring

theorem tilt_generator_sum (N_L N_R : ℝ) :
    2 * chiralTiltGenerator N_L N_R = N_L + N_R := by
  unfold chiralTiltGenerator
  ring

theorem chiral_shift_operator_unitary (θ N_L N_R : ℝ) :
    ‖chiralShiftOperator θ N_L N_R‖ = 1 := by
  unfold chiralShiftOperator
  have h_re : (Complex.I * ((θ * (N_L - N_R) : ℝ) : ℂ)).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_norm := Complex.norm_exp (Complex.I * ((θ * (N_L - N_R) : ℝ) : ℂ))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm

theorem chiral_tilt_vacuum_at_critical_equator (N_L N_R : ℝ) :
    chiralTiltOperator 0 N_L N_R = 1 := by
  unfold chiralTiltOperator
  have : (0 : ℝ) * (N_L + N_R) = 0 := by ring
  rw [this, Real.exp_zero]

theorem bost_connes_kms_vacuum (p : ℕ) (β : ℝ) :
    bostConnesKMSOperator p 0 β = 1 := by
  unfold bostConnesKMSOperator
  have : -β * Real.log (p : ℝ) * 0 = 0 := by ring
  rw [this, Real.exp_zero]

theorem grand_chiral_cuntz_algebra_synthesis
    (θ ξ N_L N_R β : ℝ) (p : ℕ) :
    (leftNullHop N_L N_R = N_L) ∧
    (rightNullHop N_L N_R = N_R) ∧
    (2 * chiralShiftGenerator N_L N_R = N_L - N_R) ∧
    (2 * chiralTiltGenerator N_L N_R = N_L + N_R) ∧
    (‖chiralShiftOperator θ N_L N_R‖ = 1) ∧
    (chiralTiltOperator 0 N_L N_R = 1) ∧
    (bostConnesKMSOperator p 0 β = 1) :=
  ⟨left_null_hop_eq_N_L N_L N_R,
   right_null_hop_eq_N_R N_L N_R,
   shift_generator_diff N_L N_R,
   tilt_generator_sum N_L N_R,
   chiral_shift_operator_unitary θ N_L N_R,
   chiral_tilt_vacuum_at_critical_equator N_L N_R,
   bost_connes_kms_vacuum p β⟩
