import InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm

/-!
# Automatic integrability for the actual local `riemannXi` period

The explicit local-zero datum keeps its integrability fields visible.  This
owner supplies the downstream convenience theorem where those fields are
derived from the differentiability hypotheses and the positive radius.
No global zero factorization or de Rham class is constructed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriodAutomatic

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeCirclePeriodBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriod
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

theorem normalized_logDifferential_circleIntegral_of_factorization_auto
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), entireRiemannXiLogDifferential z) =
      - (m : ℂ) := by
  have h_inv : CircleIntegrable (fun z : ℂ => (z - rho)⁻¹) rho R := by
    rw [circleIntegrable_sub_inv_iff]
    simp [abs_of_pos hR, hR.ne']
    exact (ne_of_gt hR).symm
  have hpole : CircleIntegrable
      (logarithmicPole rho (m : ℤ)) rho R := by
    change CircleIntegrable (fun z : ℂ => -(m : ℂ) * (z - rho)⁻¹) rho R
    simpa using h_inv.const_smul (a := -(m : ℂ))
  have hcorr : CircleIntegrable (fun z => h z / g z) rho R := by
    have hquot : DifferentiableOn ℂ (fun z => h z / g z)
        (Metric.closedBall rho R) :=
      hh.fun_div hg (fun z _ => hg0 z)
    exact hquot.continuousOn.mono Metric.sphere_subset_closedBall |>.circleIntegrable hR.le
  exact entireRiemannXi_normalized_logDifferential_circleIntegral_of_factorization
    rho m g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

theorem normalized_actual_form_unit_circleIntegral_of_factorization_auto
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R),
          actual.form z (fun _ : Fin 1 => (1 : ℂ))) =
      - (m : ℂ) := by
  have hreadout :
      (fun z : ℂ => actual.form z (fun _ : Fin 1 => (1 : ℂ))) =
        entireRiemannXiLogDifferential := by
    funext z
    simp
  rw [hreadout]
  exact normalized_logDifferential_circleIntegral_of_factorization_auto
    rho m g h hR hm hfactor hg hh hg_deriv hg0

theorem normalized_actual_form_unit_circleIntegral_integer_readout_auto
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : entireRiemannXi = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    ∃ k : ℤ,
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ z in C(rho, R),
            actual.form z (fun _ : Fin 1 => (1 : ℂ))) =
        (k : ℂ) := by
  refine ⟨-(m : ℤ), ?_⟩
  rw [normalized_actual_form_unit_circleIntegral_of_factorization_auto
    rho m g h hR hm hfactor hg hh hg_deriv hg0]
  norm_num

end InfoGeometry.Canonical.ActualEntireRiemannXiLocalZeroPeriodAutomatic
