import InfoGeometry.Canonical.ZetaLogDerivativeCirclePeriodBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Logarithmic derivatives from a local factorization

This owner supplies the calculus edge missing from the explicit circle-period
kernel: a factorization by `(z - rho)^m` gives the expected logarithmic
derivative away from the center.  The contour theorem below consumes only
explicit hypotheses; it does not assert a factorization for `riemannXi` or
any other particular analytic function.
-/

noncomputable section

namespace InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge

open Complex
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

def localLogDerivativeModel
    (rho : ℂ) (m : ℤ) (g h : ℂ → ℂ) (z : ℂ) : ℂ :=
  logarithmicPole rho m z - h z / g z

theorem localLogDerivativeModel_circleIntegral
    (rho : ℂ) (m : ℤ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg0 : ∀ z ∈ Metric.closedBall rho R, g z ≠ 0) :
    (∮ z in C(rho, R), localLogDerivativeModel rho m g h z) =
      - (m : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
  have h_inv : CircleIntegrable (fun z : ℂ => (z - rho)⁻¹) rho R := by
    rw [circleIntegrable_sub_inv_iff]
    simp [abs_of_pos hR, hR.ne']
    exact (ne_of_gt hR).symm
  have hpole : CircleIntegrable (logarithmicPole rho m) rho R := by
    change CircleIntegrable (fun z : ℂ => -(m : ℂ) * (z - rho)⁻¹) rho R
    simpa using h_inv.const_smul (a := -(m : ℂ))
  have hcorr : CircleIntegrable (fun z => h z / g z) rho R := by
    have hquot : DifferentiableOn ℂ (fun z => h z / g z)
        (Metric.closedBall rho R) := hh.fun_div hg hg0
    exact hquot.continuousOn.mono Metric.sphere_subset_closedBall |>.circleIntegrable hR.le
  calc
    (∮ z in C(rho, R), localLogDerivativeModel rho m g h z) =
        (∮ z in C(rho, R), logarithmicPole rho m z - h z / g z) := by
      rfl
    _ = (∮ z in C(rho, R), logarithmicPole rho m z) -
        (∮ z in C(rho, R), h z / g z) :=
      circleIntegral.integral_sub hpole hcorr
    _ = - (m : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
      rw [circleIntegral_div_eq_zero_of_differentiableOn_nonzero rho g h
        hR.le hg hh hg0, logarithmicPole_circleIntegral rho m hR]
      ring

theorem deriv_div_factorization
    (rho : ℂ) (m : ℕ) (f g h : ℂ → ℂ)
    (hm : 0 < m)
    (hfactor : f = fun z => (z - rho) ^ m * g z)
    (hg : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    {z : ℂ} (hz : z ≠ rho) :
    deriv f z / f z =
      (m : ℂ) / (z - rho) + h z / g z := by
  have hpow := ((hasDerivAt_id z).sub_const rho).pow m
  have hprod := hpow.mul (hg z)
  have hderiv : deriv f z =
      (m : ℂ) * (z - rho) ^ (m - 1) * g z +
        (z - rho) ^ m * h z := by
    rw [hfactor]
    simpa using hprod.deriv
  have hpow_succ : (z - rho) ^ m =
      (z - rho) ^ (m - 1) * (z - rho) := by
    rw [← Nat.sub_add_cancel hm, pow_add]
    simp [mul_comm]
  have h_sub : z - rho ≠ 0 := sub_ne_zero.mpr hz
  have h_g0 : g z ≠ 0 := hg0 z
  have h_pow0 : (z - rho) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) h_sub
  rw [hderiv]
  simp only [hfactor]
  change
    ((m : ℂ) * (z - rho) ^ (m - 1) * g z +
      (z - rho) ^ m * h z) /
        ((z - rho) ^ m * g z) =
      (m : ℂ) / (z - rho) + h z / g z
  rw [hpow_succ]
  field_simp [h_sub, h_g0, h_pow0]

theorem neg_deriv_div_factorization_eq_localLogDerivativeModel
    (rho : ℂ) (m : ℕ) (f g h : ℂ → ℂ)
    (hm : 0 < m)
    (hfactor : f = fun z => (z - rho) ^ m * g z)
    (hg : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    {z : ℂ} (hz : z ≠ rho) :
    -(deriv f z / f z) =
      localLogDerivativeModel rho (m : ℤ) g h z := by
  rw [deriv_div_factorization rho m f g h hm hfactor hg hg0 hz]
  simp [localLogDerivativeModel, logarithmicPole]
  ring

theorem neg_deriv_div_factorization_on_sphere
    (rho : ℂ) (m : ℕ) (f g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : f = fun z => (z - rho) ^ m * g z)
    (hg : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    Set.EqOn (fun z => -(deriv f z / f z))
      (fun z => logarithmicPole rho (m : ℤ) z - h z / g z)
      (Metric.sphere rho R) := by
  intro z hz
  have hzrho : z ≠ rho := by
    intro hzr
    subst z
    have : (0 : ℝ) = R := by
      simpa [Metric.mem_sphere] using hz
    linarith
  change -(deriv f z / f z) =
    logarithmicPole rho (m : ℤ) z - h z / g z
  exact neg_deriv_div_factorization_eq_localLogDerivativeModel
    rho m f g h hm hfactor hg hg0 hzrho

theorem normalized_logDerivative_circleIntegral_eq_neg_natCast
    (rho : ℂ) (m : ℕ) (f g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : f = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv f z / f z)) =
      - (m : ℂ) := by
  have hfactor' := neg_deriv_div_factorization_on_sphere rho m f g h hR hm
    hfactor hg_deriv hg0
  have hfactor'' : Set.EqOn (fun z => -(deriv f z / f z))
      (fun z => logarithmicPole rho (m : ℤ) z + (-h z) / g z)
      (Metric.sphere rho R) := by
    intro z hz
    have := hfactor' hz
    dsimp at this ⊢
    rw [this]
    ring
  have hneg_corr : CircleIntegrable (fun z => (-h z) / g z) rho R := by
    have : (fun z => (-h z) / g z) = (fun z => - (h z / g z)) := by
      ext z
      ring
    rw [this]
    exact hcorr.neg
  have h_int := polePlusHolomorphicCorrection_circleIntegral rho (m : ℤ)
    (fun z => -(deriv f z / f z)) g (fun z => -h z) hR hg (hh.neg)
    (fun z _ => hg0 z) hfactor'' hpole hneg_corr
  have hcast : ((m : ℤ) : ℂ) = (m : ℂ) := by norm_num
  rw [hcast] at h_int
  rw [h_int]
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp only [Ne, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  rw [mul_comm (- (m : ℂ)), ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

/-! The explicit integrability assumptions above are useful when transporting
the theorem across an existing contour API.  For a local analytic
factorization they are consequences of the displayed hypotheses, so expose
the theorem-honest public form as well. -/

theorem normalized_logDerivative_circleIntegral_eq_neg_natCast_derived
    (rho : ℂ) (m : ℕ) (f g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : f = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv f z / f z)) =
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
        (Metric.closedBall rho R) := hh.fun_div hg (fun z _ => hg0 z)
    exact hquot.continuousOn.mono Metric.sphere_subset_closedBall |>.circleIntegrable hR.le
  exact normalized_logDerivative_circleIntegral_eq_neg_natCast rho m f g h hR hm
    hfactor hg hh hg_deriv hg0 hpole hcorr

end InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
