import InfoGeometry.Probability.AitchisonFinite
import InfoGeometry.Analysis.LogOddsSimplexGeometry

/-!
# Binary Aitchison coordinates and log-odds geometry

The existing CLR convention uses the sum of coordinate products. Hence its
binary line element is one half of the log-odds metric. This is a coordinate
and metric identity; it supplies no experimental time evolution.
-/

noncomputable section
namespace InfoGeometry.Probability.BinaryAitchisonLogOdds

open AitchisonFinite
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry

def binary (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) : PositiveSimplex 2 :=
  ⟨![p, 1 - p], by
    constructor
    · intro i
      fin_cases i
      · simpa using hp.1
      · simpa using sub_pos.mpr hp.2
    · simp⟩

theorem clr_binary (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    clr (binary p hp) (by decide) = ![logit p / 2, -logit p / 2] := by
  have hlog : Real.log (p / (1 - p)) = Real.log p - Real.log (1 - p) :=
    Real.log_div hp.1.ne' (sub_pos.mpr hp.2).ne'
  funext i
  fin_cases i <;> simp [clr, logMean, binary, logit, hlog] <;> ring

/-- Exact bilinear normalization in the existing Aitchison convention. -/
theorem binary_inner (p q : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    AitchisonFinite.inner (binary p hp) (binary q hq) (by decide) =
      logit p * logit q / 2 := by
  unfold AitchisonFinite.inner
  rw [clr_binary, clr_binary]
  simp
  ring

/-- Euclidean squared separation after the CLR embedding. -/
theorem binary_clr_distance_sq (p q : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i : Fin 2, (clr (binary p hp) (by decide) i -
      clr (binary q hq) (by decide) i) ^ 2) = (logit p - logit q) ^ 2 / 2 := by
  rw [clr_binary, clr_binary]
  simp
  ring

/-- Squared speed of the two CLR coordinates, using actual derivatives. -/
theorem binary_clr_metric (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (deriv (fun q => logit q / 2) p) ^ 2 +
      (deriv (fun q => -logit q / 2) p) ^ 2 =
      InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric p / 2 := by
  have hneg : HasDerivAt (fun q => -logit q / 2)
      (-(1 / (p * (1 - p))) / 2) p := by
    simpa using ((hasDerivAt_logit hp).neg).div_const 2
  rw [((hasDerivAt_logit hp).div_const 2).deriv, hneg.deriv]
  unfold InfoGeometry.Probability.SimplexQuadraticResponse.logOddsMetric
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne']
  ring

/-- The established geodesic is an affine line in centered log-ratio coordinates. -/
theorem trajectory_clr (v ξ₀ t : ℝ) :
    clr (binary (trajectory v ξ₀ t) (trajectory_mem_Ioo v ξ₀ t)) (by decide) =
      ![v * t + ξ₀, -(v * t + ξ₀)] := by
  rw [clr_binary, trajectory_logit]
  congr 1 <;> ring

/-- The concrete stationary characteristic also solves the time-dependent
Hamilton--Jacobi equation after subtracting its constant energy. -/
theorem time_dependent_hamilton_jacobi (v t p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (fun s => characteristic v p - 2 * v ^ 2 * s) t +
      hamiltonian p (deriv (fun q => characteristic v q - 2 * v ^ 2 * t) p) = 0 := by
  have ht := (hasDerivAt_const t (characteristic v p)).sub
    ((hasDerivAt_id t).const_mul (2 * v ^ 2))
  change HasDerivAt (fun s => characteristic v p - 2 * v ^ 2 * s)
    (0 - 2 * v ^ 2 * 1) t at ht
  have hp' := ((hasDerivAt_logit hp).const_mul (2 * v)).sub_const (2 * v ^ 2 * t)
  rw [ht.deriv]
  change 0 - 2 * v ^ 2 * 1 + hamiltonian p
    (deriv (fun q => 2 * v * logit q - 2 * v ^ 2 * t) p) = 0
  rw [hp'.deriv]
  have h := stationary_hamilton_jacobi v hp
  change hamiltonian p (deriv (fun q => 2 * v * logit q) p) = _ at h
  rw [((hasDerivAt_logit hp).const_mul (2 * v)).deriv] at h
  linarith

end InfoGeometry.Probability.BinaryAitchisonLogOdds
