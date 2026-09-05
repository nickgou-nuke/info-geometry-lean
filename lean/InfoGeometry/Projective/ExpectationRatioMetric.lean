import InfoGeometry.Projective.Projective
import Mathlib

/-!
# Expectation ratios and a metric on the existing positive-ray quotient

The carrier is `PositiveMeasure.Proj`, not a new state type. The metric is
pulled back from the sup norm of all pairwise log ratios. On finite positive
coordinate rays this is the Hilbert projective distance. No topology
compatibility with other quotient presentations is asserted here.
-/

noncomputable section

namespace InfoGeometry.Projective.ExpectationRatioMetric

open InfoGeometry
open scoped BigOperators

variable {ι : Type*}

abbrev Weight (ι : Type*) := PositiveMeasure ι ℝ
abbrev Ray (ι : Type*) := PositiveMeasure.Proj (α := ι)

def ray (w : Weight ι) : Ray ι := Quotient.mk _ w

@[simp] theorem ray_scale (w : Weight ι) (c : ℝ) (hc : 0 < c) :
    ray (PositiveMeasure.scale c hc w) = ray w := by
  symm
  apply Quotient.sound
  exact ⟨⟨c, hc⟩, rfl⟩

/-- A homogeneous ratio, defined on the existing quotient. -/
def ratio (q : Ray ι) : ι → ι → ℝ :=
  Quotient.lift (fun w : Weight ι => fun i j => w i / w j)
    (by
      intro w v h
      rcases h with ⟨c, rfl⟩
      funext i j
      change w i / w j = (c.val * w i) / (c.val * w j)
      field_simp [c.property.ne', (w.pos j).ne'] <;> ring) q

@[simp] theorem ratio_ray (w : Weight ι) (i j : ι) :
    ratio (ray w) i j = w i / w j := rfl

theorem ratio_pos (q : Ray ι) (i j : ι) : 0 < ratio q i j := by
  refine Quotient.inductionOn q ?_
  intro w
  exact div_pos (w.pos i) (w.pos j)

@[simp] theorem ratio_self (q : Ray ι) (i : ι) : ratio q i i = 1 := by
  refine Quotient.inductionOn q ?_
  intro w
  exact div_self (w.pos i).ne'

theorem ratio_cocycle (q : Ray ι) (i j k : ι) :
    ratio q i j * ratio q j k = ratio q i k := by
  refine Quotient.inductionOn q ?_
  intro w
  change (w i / w j) * (w j / w k) = w i / w k
  field_simp [(w.pos j).ne', (w.pos k).ne'] <;> ring

/-- Two-state comparison: both state representative scales cancel. -/
def crossRatio (q r : Ray ι) (i j : ι) : ℝ := ratio q i j / ratio r i j

theorem crossRatio_ray (w v : Weight ι) (i j : ι) :
    crossRatio (ray w) (ray v) i j = (w i * v j) / (w j * v i) := by
  dsimp [crossRatio, ratio, ray]
  field_simp [(w.pos j).ne', (v.pos i).ne', (v.pos j).ne'] <;> ring

theorem crossRatio_independent_scales (w v : Weight ι) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (i j : ι) :
    crossRatio (ray (PositiveMeasure.scale c hc w))
        (ray (PositiveMeasure.scale d hd v)) i j =
      crossRatio (ray w) (ray v) i j := by
  rw [ray_scale, ray_scale]

/-- Complete finite log-ratio coordinates; no reference coordinate is preferred. -/
def logCoordinates (q : Ray ι) : ι × ι → ℝ :=
  fun ij => Real.log (ratio q ij.1 ij.2)

theorem logCoordinates_ray (w : Weight ι) (i j : ι) :
    logCoordinates (ray w) (i,j) = Real.log (w i) - Real.log (w j) := by
  exact Real.log_div (w.pos i).ne' (w.pos j).ne'

theorem log_crossRatio (q r : Ray ι) (i j : ι) :
    Real.log (crossRatio q r i j) =
      logCoordinates q (i,j) - logCoordinates r (i,j) := by
  exact Real.log_div (ratio_pos q i j).ne' (ratio_pos r i j).ne'

/-- Separation is proved for the full coordinate family, not assumed. -/
theorem ray_eq_of_ratios_eq [Nonempty ι] (w v : Weight ι)
    (h : ∀ i j, w i / w j = v i / v j) : ray w = ray v := by
  classical
  let j : ι := Classical.choice inferInstance
  apply Quotient.sound
  refine ⟨⟨v j / w j, div_pos (v.pos j) (w.pos j)⟩, ?_⟩
  apply PositiveMeasure.ext
  funext i
  change (v j / w j) * w i = v i
  calc
    (v j / w j) * w i = (w i / w j) * v j := by ring
    _ = (v i / v j) * v j := by rw [h i j]
    _ = v i := div_mul_cancel₀ _ (v.pos j).ne'

theorem logCoordinates_injective [Nonempty ι] :
    Function.Injective (logCoordinates (ι := ι)) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro w v h
  apply ray_eq_of_ratios_eq w v
  intro i j
  have hij := congrArg Real.exp (congrFun h (i,j))
  simpa only [logCoordinates, ratio_ray,
    Real.exp_log (div_pos (w.pos i) (w.pos j)),
    Real.exp_log (div_pos (v.pos i) (v.pos j))] using hij

section Finite

variable [Fintype ι] [Nonempty ι]

/-- Native metric data on the existing ray type; not a replacement state carrier. -/
def ratioMetricSpace : MetricSpace (Ray ι) :=
  MetricSpace.induced logCoordinates logCoordinates_injective inferInstance

def projectiveDistance (q r : Ray ι) : ℝ := dist (logCoordinates q) (logCoordinates r)

theorem projectiveDistance_eq_norm (q r : Ray ι) :
    projectiveDistance q r = ‖logCoordinates q - logCoordinates r‖ := dist_eq_norm _ _

theorem projectiveDistance_nonneg (q r : Ray ι) : 0 ≤ projectiveDistance q r :=
  dist_nonneg

@[simp] theorem projectiveDistance_self (q : Ray ι) : projectiveDistance q q = 0 :=
  dist_self _

theorem projectiveDistance_symm (q r : Ray ι) :
    projectiveDistance q r = projectiveDistance r q := dist_comm _ _

theorem projectiveDistance_triangle (q r s : Ray ι) :
    projectiveDistance q s ≤ projectiveDistance q r + projectiveDistance r s :=
  dist_triangle _ _ _

@[simp] theorem projectiveDistance_zero_iff (q r : Ray ι) :
    projectiveDistance q r = 0 ↔ q = r := by
  change dist (logCoordinates q) (logCoordinates r) = 0 ↔ q = r
  rw [dist_eq_zero]
  exact logCoordinates_injective.eq_iff

theorem projectiveDistance_independent_scales (w v : Weight ι) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) :
    projectiveDistance (ray (PositiveMeasure.scale c hc w))
        (ray (PositiveMeasure.scale d hd v)) = projectiveDistance (ray w) (ray v) := by
  rw [ray_scale, ray_scale]

/-- An expectation is a ratio of homogeneous weighted sums. -/
def weightedSum (w : Weight ι) (f : ι → ℝ) : ℝ := ∑ i, w i * f i

def mean (w : Weight ι) (f : ι → ℝ) : ℝ := weightedSum w f / PositiveMeasure.Z w

theorem weightedSum_scale (w : Weight ι) (f : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    weightedSum (PositiveMeasure.scale c hc w) f = c * weightedSum w f := by
  simp [weightedSum, PositiveMeasure.scale_apply, Finset.mul_sum, mul_assoc]

theorem mean_scale (w : Weight ι) (f : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    mean (PositiveMeasure.scale c hc w) f = mean w f := by
  unfold mean
  rw [weightedSum_scale, PositiveMeasure.Z_scale]
  field_simp [hc.ne', PositiveMeasure.Z_ne_zero w] <;> ring

def rayMean (q : Ray ι) (f : ι → ℝ) : ℝ :=
  Quotient.lift (fun w : Weight ι => mean w f)
    (by
      intro w v h
      rcases h with ⟨c, rfl⟩
      exact (mean_scale w f c.val c.property).symm) q

@[simp] theorem rayMean_ray (w : Weight ι) (f : ι → ℝ) :
    rayMean (ray w) f = mean w f := rfl

theorem mean_eq_sum (w : Weight ι) (f : ι → ℝ) :
    mean w f = ∑ i, PositiveMeasure.normalize w i * f i := by
  simp only [mean, weightedSum, Finset.sum_div, PositiveMeasure.normalize_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rayMean_add (q : Ray ι) (f g : ι → ℝ) :
    rayMean q (fun i => f i + g i) = rayMean q f + rayMean q g := by
  refine Quotient.inductionOn q ?_
  intro w
  simp [rayMean_ray, mean, weightedSum, mul_add, Finset.sum_add_distrib, add_div]

theorem rayMean_smul (q : Ray ι) (c : ℝ) (f : ι → ℝ) :
    rayMean q (fun i => c * f i) = c * rayMean q f := by
  refine Quotient.inductionOn q ?_
  intro w
  change (∑ i, w i * (c * f i)) / PositiveMeasure.Z w =
    c * ((∑ i, w i * f i) / PositiveMeasure.Z w)
  have hs : (∑ i, w i * (c * f i)) = c * ∑ i, w i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

@[simp] theorem rayMean_const (q : Ray ι) (c : ℝ) :
    rayMean q (fun _ => c) = c := by
  refine Quotient.inductionOn q ?_
  intro w
  change (∑ i, w i * c) / PositiveMeasure.Z w = c
  rw [← Finset.sum_mul]
  change PositiveMeasure.Z w * c / PositiveMeasure.Z w = c
  field_simp [PositiveMeasure.Z_ne_zero w] <;> ring

theorem rayMean_nonneg (q : Ray ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ rayMean q f := by
  refine Quotient.inductionOn q ?_
  intro w
  change 0 ≤ (∑ i, w i * f i) / PositiveMeasure.Z w
  exact div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (w.pos i).le (hf i))
    (PositiveMeasure.Z_pos w).le

end Finite
end InfoGeometry.Projective.ExpectationRatioMetric
