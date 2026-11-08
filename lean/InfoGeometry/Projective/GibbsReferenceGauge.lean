import InfoGeometry.Projective.GibbsRayGeometry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Removing the reference-scale gauge from Gibbs potentials

Raw log Z and entropy relative to an unnormalized reference shift when the
reference is rescaled. Their invariant combinations use Z_tilt/Z_reference
and the normalized reference probability. No raw gauge-dependent potential
is asserted to be an observable.
-/

noncomputable section
namespace InfoGeometry.Projective.GibbsReferenceGauge

open InfoGeometry
open ExpectationRatioMetric GibbsRayGeometry
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem tilt_reference_scale (w : Weight ι) (s : ι → ℝ) (β c : ℝ) (hc : 0 < c) :
    tilt (PositiveMeasure.scale c hc w) s β =
      PositiveMeasure.scale c hc (tilt w s β) := by
  apply PositiveMeasure.ext
  funext i
  dsimp [tilt, PositiveMeasure.scale]
  ring

/-- Negative KL relative to the normalized reference, rather than a raw weight. -/
def normalizedReferenceEntropy (w : Weight ι) (s : ι → ℝ) (β : ℝ) : ℝ :=
  -∑ i, PositiveMeasure.normalize (tilt w s β) i *
    Real.log (PositiveMeasure.normalize (tilt w s β) i / PositiveMeasure.normalize w i)

theorem normalizedReferenceEntropy_reference_scale (w : Weight ι) (s : ι → ℝ)
    (β c : ℝ) (hc : 0 < c) :
    normalizedReferenceEntropy (PositiveMeasure.scale c hc w) s β =
      normalizedReferenceEntropy w s β := by
  simp only [normalizedReferenceEntropy, tilt_reference_scale, PositiveMeasure.normalize_scale]

theorem normalizedReferenceEntropy_score_shift (w : Weight ι) (s : ι → ℝ) (β c : ℝ) :
    normalizedReferenceEntropy w (fun i => s i+c) β = normalizedReferenceEntropy w s β := by
  simp only [normalizedReferenceEntropy, tilt_shift, PositiveMeasure.normalize_scale]

/-- A partition comparison with its reference, invariant under reference rescaling. -/
def relativeLogPartition (w : Weight ι) (s : ι → ℝ) (β : ℝ) : ℝ :=
  logPartition w s β - Real.log (PositiveMeasure.Z w)

theorem relativeLogPartition_reference_scale (w : Weight ι) (s : ι → ℝ)
    (β c : ℝ) (hc : 0 < c) :
    relativeLogPartition (PositiveMeasure.scale c hc w) s β = relativeLogPartition w s β := by
  change Real.log (PositiveMeasure.Z (tilt (PositiveMeasure.scale c hc w) s β)) -
    Real.log (PositiveMeasure.Z (PositiveMeasure.scale c hc w)) = _
  rw [tilt_reference_scale]
  simp only [PositiveMeasure.Z_scale]
  rw [Real.log_mul hc.ne' (PositiveMeasure.Z_ne_zero (tilt w s β)),
    Real.log_mul hc.ne' (PositiveMeasure.Z_ne_zero w)]
  change Real.log c + logPartition w s β - (Real.log c + Real.log (PositiveMeasure.Z w)) = _
  unfold relativeLogPartition
  ring

theorem log_normalized_reference_probability (w : Weight ι) (s : ι → ℝ) (β : ℝ) (i : ι) :
    Real.log (PositiveMeasure.normalize (tilt w s β) i / PositiveMeasure.normalize w i) =
      β*s i - relativeLogPartition w s β := by
  rw [Real.log_div ((PositiveMeasure.normalize (tilt w s β)).pos i).ne'
    ((PositiveMeasure.normalize w).pos i).ne']
  have h := log_relative_probability w s β i
  rw [Real.log_div ((PositiveMeasure.normalize (tilt w s β)).pos i).ne' (w.pos i).ne'] at h
  rw [PositiveMeasure.normalize_apply w i,
    Real.log_div (w.pos i).ne' (PositiveMeasure.Z_ne_zero w)]
  unfold relativeLogPartition
  linarith

theorem normalizedReferenceEntropy_eq (w : Weight ι) (s : ι → ℝ) (β : ℝ) :
    normalizedReferenceEntropy w s β =
      relativeLogPartition w s β - β*rayMean (gibbsRay w s β) s := by
  unfold normalizedReferenceEntropy
  simp_rw [log_normalized_reference_probability, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hm : (∑ i, PositiveMeasure.normalize (tilt w s β) i * (β*s i)) =
      β*rayMean (gibbsRay w s β) s := by
    rw [gibbsRay, rayMean_ray, mean_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hm, ← Finset.sum_mul]
  have hz : ∑ i, PositiveMeasure.normalize (tilt w s β) i = 1 :=
    PositiveMeasure.Z_normalize _
  rw [hz]
  ring

end InfoGeometry.Projective.GibbsReferenceGauge

