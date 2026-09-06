import InfoGeometry.Canonical.ComplexAnalyticBridge

/-!
# The local logarithmic-pole period kernel

This owner contains the genuine contour-integral part of the logarithmic
residue story.  It computes the period of an explicit pole of multiplicity
`m`; it does not identify that pole with a zero of `riemannXi`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

open Complex
open InfoGeometry.Canonical.ComplexAnalyticBridge

def logarithmicPole (rho : ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  - (m : ℂ) / (z - rho)

theorem logarithmicPole_circleIntegral
    (rho : ℂ) (m : ℤ) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(rho, R), logarithmicPole rho m z) =
      - (m : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  have hdiff :
      DifferentiableOn ℂ (fun _ : ℂ => -(m : ℂ)) (Metric.closedBall rho R) :=
    differentiableOn_const (c := -(m : ℂ))
  have hmem : rho ∈ Metric.ball rho R := by
    simpa [Metric.mem_ball] using hR
  have h := cauchyIntegralFormulaOnClosedDisc
    (c := rho) (w := rho) (f := fun _ : ℂ => -(m : ℂ)) hdiff hmem
  simpa [logarithmicPole, smul_eq_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using h

theorem normalized_logarithmicPole_circleIntegral
    (rho : ℂ) (m : ℤ) {R : ℝ} (hR : 0 < R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), logarithmicPole rho m z) =
      - (m : ℂ) := by
  rw [logarithmicPole_circleIntegral rho m hR]
  field_simp

theorem circleIntegral_div_eq_zero_of_differentiableOn_nonzero
    (rho : ℂ) (g h : ℂ → ℂ)
    {R : ℝ} (hR : 0 ≤ R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg0 : ∀ z ∈ Metric.closedBall rho R, g z ≠ 0)
    :
    (∮ z in C(rho, R), h z / g z) = 0 := by
  have hquot :
      DifferentiableOn ℂ (fun z => h z / g z) (Metric.closedBall rho R) :=
    hh.fun_div hg hg0
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (c := rho) (f := fun z => h z / g z) (s := ∅) hR Set.countable_empty
    hquot.continuousOn (fun z hz =>
      (hquot z (Metric.ball_subset_closedBall hz.1)).differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz.1))

theorem polePlusHolomorphicCorrection_circleIntegral
    (rho : ℂ) (m : ℤ) (f g h : ℂ → ℂ)
    {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg0 : ∀ z ∈ Metric.closedBall rho R, g z ≠ 0)
    (hfactor : Set.EqOn f
      (fun z => logarithmicPole rho m z + h z / g z)
      (Metric.sphere rho R))
    (hpole : CircleIntegrable (logarithmicPole rho m) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (∮ z in C(rho, R), f z) =
      - (m : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  have hcorr_zero := circleIntegral_div_eq_zero_of_differentiableOn_nonzero
    rho g h hR.le hg hh hg0
  calc
    (∮ z in C(rho, R), f z) =
        ∮ z in C(rho, R), logarithmicPole rho m z + h z / g z :=
      circleIntegral.integral_congr hR.le hfactor
    _ = (∮ z in C(rho, R), logarithmicPole rho m z) +
        (∮ z in C(rho, R), h z / g z) :=
      circleIntegral.integral_add hpole hcorr
    _ = - (m : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
      rw [hcorr_zero, logarithmicPole_circleIntegral rho m hR]
      ring

end InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod
