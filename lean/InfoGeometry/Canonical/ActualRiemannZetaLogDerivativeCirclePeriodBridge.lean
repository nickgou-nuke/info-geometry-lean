import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
import InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
import InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-!
# Local logarithmic period for the actual Riemann zeta function

This owner specializes the repository's zero-free circle-integral kernel to
Mathlib's `riemannZeta`.  Regularity and nonvanishing on the disk remain
explicit hypotheses; no analytic continuation or zero classification is
silently introduced.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical.ActualRiemannZetaLogDerivativeCirclePeriodBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
open InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy
open InfoGeometry.Canonical.LogDerivativeLocalFactorizationBridge
open InfoGeometry.Canonical.ZetaLogarithmicPoleCirclePeriod

/-! The local factorization theorem is the actual zeta specialization of the
generic logarithmic-derivative residue kernel.  The factorization and
nonvanishing hypotheses remain explicit; no global zero classification is
introduced. -/

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannZeta = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0)
    (hpole : CircleIntegrable
      (ZetaLogarithmicPoleCirclePeriod.logarithmicPole rho (m : ℤ)) rho R)
    (hcorr : CircleIntegrable (fun z => h z / g z) rho R) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) =
      - (m : ℂ) := by
  simpa only [actualRiemannZetaLogDerivative, neg_div] using
    normalized_logDerivative_circleIntegral_eq_neg_natCast
      rho m riemannZeta g h hR hm hfactor hg hh hg_deriv hg0 hpole hcorr

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_of_factorization_derived
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannZeta = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) =
      - (m : ℂ) := by
    simpa only [actualRiemannZetaLogDerivative, neg_div] using
    normalized_logDerivative_circleIntegral_eq_neg_natCast_derived
      rho m riemannZeta g h hR hm hfactor hg hh hg_deriv hg0

/-! The ordinary logarithmic derivative has the opposite sign from the
von-Mangoldt convention above.  This is the residue/order readout in the
usual convention `ζ'/ζ`. -/

theorem actualRiemannZeta_normalized_derivative_div_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannZeta = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), deriv riemannZeta z / riemannZeta z) =
      (m : ℂ) := by
  have hperiod :=
    normalized_logDerivative_circleIntegral_eq_neg_natCast_derived
      rho m riemannZeta g h hR hm hfactor hg hh hg_deriv hg0
  have hneg :
      (∮ z in C(rho, R), -(deriv riemannZeta z / riemannZeta z)) =
        (-1 : ℂ) • (∮ z in C(rho, R),
          deriv riemannZeta z / riemannZeta z) := by
    rw [← circleIntegral.integral_smul]
    congr 1
    funext z
    simp
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), deriv riemannZeta z / riemannZeta z) =
      - ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), -(deriv riemannZeta z / riemannZeta z))) := by
          rw [hneg]
          simp only [smul_eq_mul, neg_one_mul]
          ring
    _ = - (-(m : ℂ)) := by rw [hperiod]
    _ = (m : ℂ) := by ring

/-! The same residue readout in Mathlib's native `logDeriv` notation. -/

theorem actualRiemannZeta_normalized_logDeriv_circleIntegral_of_factorization
    (rho : ℂ) (m : ℕ) (g h : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hm : 0 < m)
    (hfactor : riemannZeta = fun z => (z - rho) ^ m * g z)
    (hg : DifferentiableOn ℂ g (Metric.closedBall rho R))
    (hh : DifferentiableOn ℂ h (Metric.closedBall rho R))
    (hg_deriv : ∀ z, HasDerivAt g (h z) z)
    (hg0 : ∀ z, g z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), logDeriv riemannZeta z) =
      (m : ℂ) := by
  simpa [logDeriv] using
    actualRiemannZeta_normalized_derivative_div_circleIntegral_of_factorization
      rho m g h hR hm hfactor hg hh hg_deriv hg0

/-! ## Finite aggregation into the divisor-index owner -/

/-- A finite family of local zeta period readouts aggregates to the cast
finite divisor index.  The local period equations remain explicit hypotheses;
this theorem does not enumerate the global zero set or assert a Hadamard
factorization. -/
theorem finite_normalized_logDeriv_circle_period_eq_cast_divisorIndex
    {ι : Type*} [Fintype ι]
    (rho : ι → ℂ) (R : ι → ℝ) (m : ι → ℕ)
    (hperiod : ∀ a : ι,
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ z in C(rho a, R a), logDeriv riemannZeta z) =
        (m a : ℂ)) :
    ∑ a : ι,
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ z in C(rho a, R a), logDeriv riemannZeta z)) =
      (divisorIndex (fun a => (m a : ℤ)) : ℂ) := by
  simp only [hperiod]
  simp [divisorIndex]

theorem actualRiemannZeta_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R))
    (hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R))
    (hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0) :
    (∮ z in C(rho, R),
      actualRiemannZetaLogDerivative z) = 0 := by
  have hquot := circleIntegral_div_eq_zero_of_differentiableOn_nonzero
    rho riemannZeta (deriv riemannZeta) hR.le hζ hderiv hzero
  calc
    (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) =
        (-1 : ℂ) •
          (∮ z in C(rho, R), deriv riemannZeta z / riemannZeta z) := by
      rw [← circleIntegral.integral_smul]
      congr 1
      funext z
      simp [actualRiemannZetaLogDerivative, neg_div]
    _ = 0 := by
      rw [hquot]
      simp

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R))
    (hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R))
    (hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) = 0 := by
  rw [actualRiemannZeta_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR hζ hderiv hzero]
  simp

theorem actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_one_lt_re
    (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hRe : ∀ z ∈ Metric.closedBall rho R, 1 < z.re) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (∮ z in C(rho, R), actualRiemannZetaLogDerivative z) = 0 := by
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hζU : DifferentiableOn ℂ riemannZeta U := by
    intro z hz
    change 1 < z.re at hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_riemannZeta
    show z ≠ (1 : ℂ)
    intro hz1
    rw [hz1] at hz
    norm_num at hz
  have hsubset : Metric.closedBall rho R ⊆ U := by
    intro z hz
    exact hRe z hz
  have hζ : DifferentiableOn ℂ riemannZeta (Metric.closedBall rho R) :=
    hζU.mono hsubset
  have hderiv : DifferentiableOn ℂ (deriv riemannZeta)
      (Metric.closedBall rho R) :=
    (hζU.deriv hUopen).mono hsubset
  have hzero : ∀ z ∈ Metric.closedBall rho R, riemannZeta z ≠ 0 := by
    intro z hz
    exact riemannZeta_ne_zero_of_one_lt_re (hRe z hz)
  exact actualRiemannZeta_normalized_logDerivative_circleIntegral_eq_zero_of_nonvanishing
    rho hR hζ hderiv hzero

end InfoGeometry.Canonical.ActualRiemannZetaLogDerivativeCirclePeriodBridge
