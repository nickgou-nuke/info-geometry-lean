import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SelfConcordantZetaBarrier

/-!
# Natural-gradient Lyapunov dynamics for the Itakura--Saito kernel

The construction is restricted to the positive half-line.  It proves the
finite Lie-derivative identity, not global existence or convergence of an ODE.
-/

namespace InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

open InfoGeometry.Canonical.SelfConcordantZetaBarrier

noncomputable section

def lyapunovPotential (x : ℝ) : ℝ := isBarrierKernel x

def hessianMetric (x : ℝ) : ℝ := isBarrierKernel_deriv2 x

def naturalGradientField (κ x : ℝ) : ℝ :=
  -κ * x ^ 2 * isBarrierKernel_deriv x

theorem lyapunovPotential_nonneg (x : ℝ) (hx : 0 < x) :
    0 ≤ lyapunovPotential x := by
  exact isBarrierKernel_nonneg x hx

theorem lyapunovPotential_eq_zero_iff (x : ℝ) (hx : 0 < x) :
    lyapunovPotential x = 0 ↔ x = 1 := by
  exact isBarrierKernel_eq_zero_iff x hx

theorem hessianMetric_eq (x : ℝ) :
    hessianMetric x = 1 / x ^ 2 := by
  rfl

theorem hessianMetric_pos (x : ℝ) (hx : 0 < x) :
    0 < hessianMetric x := by
  exact isBarrierKernel_deriv2_pos x hx

theorem naturalGradientField_eq (κ x : ℝ) (hx : x ≠ 0) :
    naturalGradientField κ x = -κ * x * (x - 1) := by
  unfold naturalGradientField isBarrierKernel_deriv
  field_simp

theorem naturalGradientField_zero_iff (κ x : ℝ) (hκ : 0 < κ) (hx : 0 < x) :
    naturalGradientField κ x = 0 ↔ x = 1 := by
  rw [naturalGradientField_eq κ x (ne_of_gt hx)]
  constructor
  · intro h
    have hκx : κ * x ≠ 0 := mul_ne_zero (ne_of_gt hκ) (ne_of_gt hx)
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp (by simpa [neg_eq_zero] using h)).resolve_left hκx
  · intro h
    rw [h]
    ring

def lyapunovLieDerivative (κ x : ℝ) : ℝ :=
  (1 - 1 / x) * naturalGradientField κ x

theorem lyapunovLieDerivative_eq (κ x : ℝ) (hx : x ≠ 0) :
    lyapunovLieDerivative κ x = -κ * (x - 1) ^ 2 := by
  unfold lyapunovLieDerivative
  rw [naturalGradientField_eq κ x hx]
  field_simp

theorem lyapunovLieDerivative_nonpos (κ x : ℝ)
    (hκ : 0 ≤ κ) (hx : x ≠ 0) :
    lyapunovLieDerivative κ x ≤ 0 := by
  rw [lyapunovLieDerivative_eq κ x hx]
  nlinarith [sq_nonneg (x - 1)]

theorem lyapunovLieDerivative_neg (κ x : ℝ)
    (hκ : 0 < κ) (hx : x ≠ 0) (hne : x ≠ 1) :
    lyapunovLieDerivative κ x < 0 := by
  rw [lyapunovLieDerivative_eq κ x hx]
  have hs : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith [hs]

theorem naturalGradientField_pos_below (κ x : ℝ)
    (hκ : 0 < κ) (hx : 0 < x) (hbelow : x < 1) :
    0 < naturalGradientField κ x := by
  rw [naturalGradientField_eq κ x (ne_of_gt hx)]
  have : x - 1 < 0 := sub_neg.mpr hbelow
  have hκx : 0 < κ * x := mul_pos hκ hx
  have hneg : -κ * x < 0 := by nlinarith
  exact mul_pos_of_neg_of_neg hneg this

theorem naturalGradientField_neg_above (κ x : ℝ)
    (hκ : 0 < κ) (hbelow : 1 < x) :
    naturalGradientField κ x < 0 := by
  rw [naturalGradientField_eq κ x (ne_of_gt (lt_trans (by positivity) hbelow))]
  have hx : 0 < x := by linarith
  have hκx : 0 < κ * x := mul_pos hκ hx
  have hneg : -κ * x < 0 := by nlinarith
  exact mul_neg_of_neg_of_pos hneg (sub_pos.mpr hbelow)

theorem global_selfConcordant_lyapunov (κ x : ℝ)
    (hκ : 0 < κ) (hx : 0 < x) :
    0 ≤ lyapunovPotential x ∧
      (lyapunovPotential x = 0 ↔ x = 1) ∧
      0 < hessianMetric x ∧
      lyapunovLieDerivative κ x ≤ 0 ∧
      (lyapunovLieDerivative κ x = 0 ↔ x = 1) := by
  refine ⟨lyapunovPotential_nonneg x hx,
    lyapunovPotential_eq_zero_iff x hx,
    hessianMetric_pos x hx,
    lyapunovLieDerivative_nonpos κ x hκ.le (ne_of_gt hx), ?_⟩
  rw [lyapunovLieDerivative_eq κ x (ne_of_gt hx)]
  constructor
  · intro h
    have : (x - 1) ^ 2 = 0 := by nlinarith
    nlinarith
  · intro h
    rw [h]
    ring

end

end InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov
