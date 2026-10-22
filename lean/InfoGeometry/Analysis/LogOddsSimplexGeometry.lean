/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AmariBinarySimplexBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Probability.SimplexQuadraticResponse
import InfoGeometry.Probability.FisherRaoMadelungIsometry

/-!
# Two geometries of the binary simplex

Extends the existing Amari binary owner using actual Mathlib derivatives.
The Fisher metric is `1/(p*(1-p))`. The different metric studied here is
the pullback of Euclidean length by `logit`, namely its square.
An affine logit trajectory solves the latter metric's coordinate geodesic
equation. Its parameter is mathematical, not an experimental relaxation time.
CAS cross-check: `scripts/verify_simplex_response.py`.
-/

noncomputable section
namespace InfoGeometry.Analysis.LogOddsSimplexGeometry

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Probability.FisherRaoMadelungIsometry
open InfoGeometry.Probability.SimplexQuadraticResponse (logOddsMetric)

/-- Native derivative strengthening of the existing logistic chart. -/
theorem hasDerivAt_logistic (θ : ℝ) :
    HasDerivAt logistic (logistic θ * (1 - logistic θ)) θ := by
  have hd : DifferentiableAt ℝ logistic θ := by
    unfold logistic
    exact (Real.hasDerivAt_exp θ).differentiableAt.div
      ((Real.hasDerivAt_exp θ).const_add 1).differentiableAt (by positivity)
  simpa [deriv_logistic, fisherExp] using hd.hasDerivAt

/-- Native derivative of the inverse chart on its open domain. -/
theorem hasDerivAt_logit {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt logit (1 / (p * (1 - p))) p := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  have hq : HasDerivAt (fun x => 1 - x) (0 - 1) p :=
    (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hr := ((hasDerivAt_id p).div hq hq0).log (div_ne_zero hp0 hq0)
  have hderiv_eq : ((1 * (1 - p) - p * (0 - 1)) / (1 - p) ^ 2) / (p / (1 - p)) =
      1 / (p * (1 - p)) := by
    field_simp [hp0, hq0]
    ring
  exact hr.congr_deriv hderiv_eq

theorem hasDerivAt_fisherMix {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt fisherMix ((2 * p - 1) / (p * (1 - p)) ^ 2) p := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  have hq : HasDerivAt (fun x => 1 - x) (0 - 1) p :=
    (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hprod := (hasDerivAt_id p).mul hq
  have hdiv := (hasDerivAt_const p (1 : ℝ)).div hprod (mul_ne_zero hp0 hq0)
  have hderiv_eq : (0 * (p * (1 - p)) - 1 * (1 * (1 - p) + p * (0 - 1))) /
      (p * (1 - p)) ^ 2 = (2 * p - 1) / (p * (1 - p)) ^ 2 := by
    ring
  exact hdiv.congr_deriv hderiv_eq

/-- Scalar Levi-Civita coefficient computed from the actual metric derivative. -/
theorem logOdds_connection {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    deriv logOddsMetric p / (2 * logOddsMetric p) = (2 * p - 1) / (p * (1 - p)) := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  have hd := (hasDerivAt_fisherMix hp).pow 2
  have hfun : logOddsMetric = fisherMix ^ 2 := by
    funext x
    change 1 / (x * (1 - x)) ^ 2 = (1 / (x * (1 - x))) ^ 2
    rw [div_pow, one_pow]
  rw [hfun, hd.deriv]
  simp only [Pi.pow_apply, fisherMix, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by decide, pow_one]
  field_simp [hp0, hq0]

/-- In Fisher geometry the square-root amplitudes have the native speed
predicted by the existing Madelung isometry. -/
theorem binary_amplitude_speed (p : ℝ → ℝ) (u t : ℝ)
    (hd : HasDerivAt p u t) (hp : p t ∈ Set.Ioo (0 : ℝ) 1) :
    4 * ((deriv (fun s => Real.sqrt (p s)) t) ^ 2 +
      (deriv (fun s => Real.sqrt (1 - p s)) t) ^ 2) =
      fisherMix (p t) * u ^ 2 := by
  have hq : HasDerivAt (fun s => 1 - p s) (-u) t := by
    have hsub := (hasDerivAt_const t (1 : ℝ)).sub hd
    rw [← zero_sub u]
    exact hsub
  have hfirst := fisher_rao_madelung_deriv p u t hd hp.1
  have hsecond := fisher_rao_madelung_deriv (fun s => 1 - p s) (-u) t
    hq (sub_pos.mpr hp.2)
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  calc
    _ = u ^ 2 / p t + (-u) ^ 2 / (1 - p t) := by linarith
    _ = _ := by unfold fisherMix; field_simp; ring

/-- Affine motion in half-logit coordinates, using the existing logistic map. -/
def trajectory (v ξ₀ t : ℝ) : ℝ := logistic (2 * (v * t + ξ₀))

theorem trajectory_mem_Ioo (v ξ₀ t : ℝ) :
    trajectory v ξ₀ t ∈ Set.Ioo (0 : ℝ) 1 :=
  logistic_mem_Ioo _

theorem trajectory_logit (v ξ₀ t : ℝ) :
    logit (trajectory v ξ₀ t) = 2 * (v * t + ξ₀) :=
  logit_logistic _

theorem hasDerivAt_trajectory (v ξ₀ t : ℝ) :
    HasDerivAt (trajectory v ξ₀)
      (2 * v * trajectory v ξ₀ t * (1 - trajectory v ξ₀ t)) t := by
  have hin := (((hasDerivAt_id t).const_mul v).add_const ξ₀).const_mul 2
  have h := (hasDerivAt_logistic (2 * (v * t + ξ₀))).comp t hin
  have hderiv_eq : logistic (2 * (v * t + ξ₀)) * (1 - logistic (2 * (v * t + ξ₀))) * (2 * (v * 1)) =
      2 * v * trajectory v ξ₀ t * (1 - trajectory v ξ₀ t) := by
    dsimp [trajectory]
    ring
  exact h.congr_deriv hderiv_eq

/-- The square-root amplitudes of the logistic curve have squared speed
equal to the Fisher susceptibility in its scaled logit coordinate. -/
theorem logistic_curve_amplitude_speed (slope t : ℝ) :
    4 * ((deriv (fun s : ℝ => Real.sqrt (logistic (slope * s))) t) ^ 2 +
      (deriv (fun s : ℝ => Real.sqrt (1 - logistic (slope * s))) t) ^ 2) =
      slope ^ 2 * fisherExp (slope * t) := by
  let p : ℝ → ℝ := fun s => trajectory (slope / 2) 0 s
  let θ := slope * t
  have htrajectory : trajectory (slope / 2) 0 t = logistic θ := by
    dsimp [trajectory, θ]
    congr 1
    ring
  have hpt : p t = logistic θ := by
    exact htrajectory
  have hd : HasDerivAt p (slope * fisherExp θ) t := by
    have h := hasDerivAt_trajectory (slope / 2) 0 t
    have hvalue :
        2 * (slope / 2) * trajectory (slope / 2) 0 t *
            (1 - trajectory (slope / 2) 0 t) = slope * fisherExp θ := by
      rw [htrajectory, fisherExp_eq_logistic_mul_complement]
      ring
    simpa [p] using h.congr_deriv hvalue
  have hp : p t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [p] using trajectory_mem_Ioo (slope / 2) 0 t
  have hamplitude := binary_amplitude_speed p (slope * fisherExp θ) t hd hp
  have hfun : p = fun s : ℝ => logistic (slope * s) := by
    funext s
    dsimp [p, trajectory]
    congr 1
    ring
  rw [hfun] at hamplitude
  have hrecip : fisherMix (logistic θ) * fisherExp θ = 1 := by
    calc
      _ = fisherMix (logistic θ) * fisherExp (logit (logistic θ)) := by
        rw [logit_logistic]
      _ = 1 := fisherMix_mul_fisherExp_logit (logistic_mem_Ioo θ)
  have hscale :
      fisherMix (logistic θ) * (slope * fisherExp θ) ^ 2 =
        slope ^ 2 * fisherExp θ := by
    calc
      _ = slope ^ 2 * fisherExp θ *
          (fisherMix (logistic θ) * fisherExp θ) := by ring
      _ = slope ^ 2 * fisherExp θ := by rw [hrecip]; ring
  calc
    _ = fisherMix (logistic θ) * (slope * fisherExp θ) ^ 2 := hamplitude
    _ = slope ^ 2 * fisherExp θ := hscale

theorem trajectory_acceleration (v ξ₀ t : ℝ) :
    deriv (deriv (trajectory v ξ₀)) t =
      4 * v ^ 2 * trajectory v ξ₀ t * (1 - trajectory v ξ₀ t) *
        (1 - 2 * trajectory v ξ₀ t) := by
  have hf : deriv (trajectory v ξ₀) =
      fun s => 2 * v * trajectory v ξ₀ s * (1 - trajectory v ξ₀ s) := by
    funext s
    exact (hasDerivAt_trajectory v ξ₀ s).deriv
  rw [hf]
  have hd := hasDerivAt_trajectory v ξ₀ t
  convert ((hd.const_mul (2 * v)).mul ((hasDerivAt_const t (1 : ℝ)).sub hd)).deriv using 1
  dsimp
  ring

/-- The coordinate geodesic equation, with genuine first and second derivatives. -/
theorem trajectory_geodesic (v ξ₀ t : ℝ) :
    deriv (deriv (trajectory v ξ₀)) t +
      deriv logOddsMetric (trajectory v ξ₀ t) / (2 * logOddsMetric (trajectory v ξ₀ t)) *
        (deriv (trajectory v ξ₀) t) ^ 2 = 0 := by
  have hp := trajectory_mem_Ioo v ξ₀ t
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  rw [trajectory_acceleration, logOdds_connection hp, (hasDerivAt_trajectory v ξ₀ t).deriv]
  field_simp
  ring

def hamiltonian (p π : ℝ) : ℝ := (p * (1 - p)) ^ 2 * π ^ 2 / 2

/-- Momentum evaluated on the affine-logit family. -/
def momentum (v p : ℝ) : ℝ := 2 * v / (p * (1 - p))

theorem hamiltonian_on_momentum (v : ℝ) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    hamiltonian p (momentum v p) = 2 * v ^ 2 := by
  have hp0 := hp.1.ne'
  have hq0 := (sub_pos.mpr hp.2).ne'
  unfold hamiltonian momentum
  field_simp

/-- Characteristic function in the same canonical chart. -/
def characteristic (v p : ℝ) : ℝ := 2 * v * logit p

/-- Hamilton--Jacobi uses an actual gradient of a concrete function. -/
theorem stationary_hamilton_jacobi (v : ℝ) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    hamiltonian p (deriv (characteristic v) p) = 2 * v ^ 2 := by
  have hd := (hasDerivAt_logit hp).const_mul (2 * v)
  change hamiltonian p (deriv (fun x => 2 * v * logit x) p) = _
  rw [hd.deriv]
  have hm : 2 * v * (1 / (p * (1 - p))) = momentum v p := by
    unfold momentum
    ring
  rw [hm]
  exact hamiltonian_on_momentum v hp

end InfoGeometry.Analysis.LogOddsSimplexGeometry
