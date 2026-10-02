import InfoGeometry.Convex.HessianGeometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Topology

noncomputable section

namespace InfoGeometry.Epistemology.NaturalGradientDissipation

open InfoGeometry.Convex
open HessianGeometry1D

def divergenceGradient (geometry : HessianGeometry1D) (point target : ℝ) : ℝ :=
  geometry.dualMap point - geometry.dualMap target

def naturalVelocity (geometry : HessianGeometry1D) (point target : ℝ) : ℝ :=
  -divergenceGradient geometry point target / geometry.metric point

def dissipation (geometry : HessianGeometry1D) (point target : ℝ) : ℝ :=
  divergenceGradient geometry point target ^ 2 / geometry.metric point

theorem hasDerivAt_divergence (geometry : HessianGeometry1D) (point target : ℝ)
    (differentiable : DifferentiableAt ℝ geometry.potential point) :
    HasDerivAt (fun value => geometry.divergence value target)
      (divergenceGradient geometry point target) point := by
  convert (differentiable.hasDerivAt.sub_const (geometry.potential target)).sub
    (((hasDerivAt_id point).sub_const target).const_mul (geometry.dualMap target)) using 1
  simp [divergenceGradient, dualMap]

theorem hasDerivAt_divergence_along_flow (geometry : HessianGeometry1D)
    (trajectory : ℝ → ℝ) (target time : ℝ)
    (differentiable : DifferentiableAt ℝ geometry.potential (trajectory time))
    (flow : HasDerivAt trajectory (naturalVelocity geometry (trajectory time) target) time) :
    HasDerivAt (fun instant => geometry.divergence (trajectory instant) target)
      (-dissipation geometry (trajectory time) target) time := by
  convert (hasDerivAt_divergence geometry (trajectory time) target differentiable).comp time flow
    using 1
  unfold naturalVelocity dissipation
  ring

theorem dissipation_nonneg (geometry : HessianGeometry1D) (point target : ℝ)
    (metric_positive : 0 < geometry.metric point) :
    0 ≤ dissipation geometry point target :=
  div_nonneg (sq_nonneg _) metric_positive.le

theorem divergence_antitone (geometry : HessianGeometry1D)
    (trajectory : ℝ → ℝ) (target : ℝ)
    (differentiable : ∀ time, DifferentiableAt ℝ geometry.potential (trajectory time))
    (flow : ∀ time, HasDerivAt trajectory
      (naturalVelocity geometry (trajectory time) target) time)
    (metric_positive : ∀ time, 0 < geometry.metric (trajectory time)) :
    Antitone (fun time => geometry.divergence (trajectory time) target) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun time => hasDerivAt_divergence_along_flow geometry trajectory target time
      (differentiable time) (flow time))
  intro time
  exact neg_nonpos.mpr (dissipation_nonneg geometry (trajectory time) target (metric_positive time))

theorem divergence_exponential_bound (geometry : HessianGeometry1D)
    (trajectory : ℝ → ℝ) (target rate time : ℝ)
    (differentiable : ∀ instant, DifferentiableAt ℝ geometry.potential (trajectory instant))
    (flow : ∀ instant, HasDerivAt trajectory
      (naturalVelocity geometry (trajectory instant) target) instant)
    (domination : ∀ instant, rate * geometry.divergence (trajectory instant) target ≤
      dissipation geometry (trajectory instant) target)
    (time_nonneg : 0 ≤ time) :
    geometry.divergence (trajectory time) target ≤
      geometry.divergence (trajectory 0) target * Real.exp (-rate * time) := by
  have weighted_derivative (instant : ℝ) :
      HasDerivAt (fun parameter => Real.exp (rate * parameter) *
        geometry.divergence (trajectory parameter) target)
        (Real.exp (rate * instant) * (rate * geometry.divergence (trajectory instant) target -
          dissipation geometry (trajectory instant) target)) instant := by
    convert (((hasDerivAt_id instant).const_mul rate).exp).mul
      (hasDerivAt_divergence_along_flow geometry trajectory target instant
        (differentiable instant) (flow instant)) using 1
    simp only [id_eq]
    ring
  have decreasing := antitone_of_hasDerivAt_nonpos weighted_derivative (fun instant =>
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (domination instant)))
  have bound : Real.exp (rate * time) * geometry.divergence (trajectory time) target ≤
      geometry.divergence (trajectory 0) target := by
    simpa using decreasing time_nonneg
  have divided : geometry.divergence (trajectory time) target ≤
      geometry.divergence (trajectory 0) target / Real.exp (rate * time) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using bound)
  simpa only [div_eq_mul_inv, neg_mul, Real.exp_neg] using divided

theorem divergence_tendsto_zero (geometry : HessianGeometry1D)
    (trajectory : ℝ → ℝ) (target rate : ℝ) (rate_positive : 0 < rate)
    (differentiable : ∀ instant, DifferentiableAt ℝ geometry.potential (trajectory instant))
    (flow : ∀ instant, HasDerivAt trajectory
      (naturalVelocity geometry (trajectory instant) target) instant)
    (domination : ∀ instant, rate * geometry.divergence (trajectory instant) target ≤
      dissipation geometry (trajectory instant) target)
    (nonnegative : ∀ instant, 0 ≤ geometry.divergence (trajectory instant) target) :
    Filter.Tendsto (fun instant => geometry.divergence (trajectory instant) target)
      Filter.atTop (𝓝 0) := by
  have scaled : Filter.Tendsto (fun instant : ℝ => rate * instant)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop rate_positive Filter.tendsto_id
  have exponential := Real.tendsto_exp_neg_atTop_nhds_zero.comp scaled
  have bound_limit : Filter.Tendsto (fun instant : ℝ =>
      geometry.divergence (trajectory 0) target * Real.exp (-rate * instant))
      Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_mul, mul_zero] using
      exponential.const_mul (geometry.divergence (trajectory 0) target)
  apply squeeze_zero' (Filter.Eventually.of_forall nonnegative) ?_ bound_limit
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with instant instant_nonneg
  exact divergence_exponential_bound geometry trajectory target rate instant
    differentiable flow domination instant_nonneg

end InfoGeometry.Epistemology.NaturalGradientDissipation
