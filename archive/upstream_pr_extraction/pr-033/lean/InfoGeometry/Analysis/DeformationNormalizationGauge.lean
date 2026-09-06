import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace InfoGeometry.Analysis.DeformationNormalizationGauge

variable {X : Type*}

/-- Normalize a scalar weight by a nonzero scalar partition factor. -/
def normalizedWeight
    (weight : X → ℝ)
    (Z : ℝ) :
    X → ℝ :=
  fun x => weight x / Z

/-- Pointwise surprisal of an unnormalized scalar weight. -/
def unnormalizedSurprisal
    (weight : X → ℝ)
    (x : X) : ℝ :=
  -Real.log (weight x)

/-- Pointwise surprisal after scalar normalization. -/
def normalizedSurprisal
    (weight : X → ℝ)
    (Z : ℝ)
    (x : X) : ℝ :=
  -Real.log (normalizedWeight weight Z x)

/--
Normalization adds the scalar gauge `log Z` to pointwise surprisal.
-/
theorem normalizedSurprisal_eq_unnormalized_add_log
    (weight : X → ℝ)
    (Z : ℝ)
    (x : X)
    (hw : weight x ≠ 0)
    (hZ : Z ≠ 0) :
    normalizedSurprisal weight Z x =
      unnormalizedSurprisal weight x +
        Real.log Z := by
  unfold normalizedSurprisal normalizedWeight unnormalizedSurprisal
  rw [Real.log_div hw hZ]
  ring

/-- Positive-weight specialization of the normalization-gauge identity. -/
theorem normalizedSurprisal_eq_unnormalized_add_log_of_pos
    (weight : X → ℝ)
    (Z : ℝ)
    (x : X)
    (hw : 0 < weight x)
    (hZ : 0 < Z) :
    normalizedSurprisal weight Z x =
      unnormalizedSurprisal weight x +
        Real.log Z :=
  normalizedSurprisal_eq_unnormalized_add_log
    weight Z x (ne_of_gt hw) (ne_of_gt hZ)

/--
The scalar normalization gauge cancels from differences of pointwise
surprisal.
-/
theorem normalizedSurprisal_sub
    (weight : X → ℝ)
    (Z : ℝ)
    (x y : X)
    (hx : weight x ≠ 0)
    (hy : weight y ≠ 0)
    (hZ : Z ≠ 0) :
    normalizedSurprisal weight Z x -
        normalizedSurprisal weight Z y =
      unnormalizedSurprisal weight x -
        unnormalizedSurprisal weight y := by
  rw [normalizedSurprisal_eq_unnormalized_add_log
      weight Z x hx hZ,
    normalizedSurprisal_eq_unnormalized_add_log
      weight Z y hy hZ]
  ring

/-- Positive-weight specialization of normalization-gauge cancellation. -/
theorem normalizedSurprisal_sub_of_pos
    (weight : X → ℝ)
    (Z : ℝ)
    (x y : X)
    (hx : 0 < weight x)
    (hy : 0 < weight y)
    (hZ : 0 < Z) :
    normalizedSurprisal weight Z x -
        normalizedSurprisal weight Z y =
      unnormalizedSurprisal weight x -
        unnormalizedSurprisal weight y :=
  normalizedSurprisal_sub weight Z x y
    (ne_of_gt hx) (ne_of_gt hy) (ne_of_gt hZ)

/--
Simultaneously scaling the unnormalized weight and partition factor leaves
the normalized weight unchanged.
-/
theorem normalizedWeight_scale
    (weight : X → ℝ)
    (Z c : ℝ)
    (hZ : Z ≠ 0)
    (hc : c ≠ 0) :
    normalizedWeight (fun x => c * weight x) (c * Z) =
      normalizedWeight weight Z := by
  funext x
  unfold normalizedWeight
  field_simp

end InfoGeometry.Analysis.DeformationNormalizationGauge
