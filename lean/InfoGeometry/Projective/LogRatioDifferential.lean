import InfoGeometry.Projective.ExpectationRatioMetric
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analytic.LogSumExp

/-!
# Horizontal logarithmic differentials and finite Fisher energy

Directions are variations of positive state representatives. A radial
variation is gauge. No coordinate is declared temporal or spatial.
-/

noncomputable section
namespace InfoGeometry.Projective.LogRatioDifferential

open InfoGeometry
open ExpectationRatioMetric
open scoped BigOperators

variable {ι : Type*}

/-- Differential of all pairwise log ratios, bundled as a native linear map. -/
def logDifferential (w : Weight ι) : (ι → ℝ) →ₗ[ℝ] (ι × ι → ℝ) where
  toFun v ij := v ij.1 / w ij.1 - v ij.2 / w ij.2
  map_add' v z := by
    funext ij
    simp only [Pi.add_apply, add_div]
    ring
  map_smul' c v := by
    funext ij
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem logDifferential_apply (w : Weight ι) (v : ι → ℝ) (i j : ι) :
    logDifferential w v (i,j) = v i / w i - v j / w j := rfl

/-- Actual derivative along an affine variation through a positive representative. -/
theorem hasDerivAt_logRatios (w : Weight ι) (v : ι → ℝ) (i j : ι) :
    HasDerivAt (fun t : ℝ => Real.log (w i + t * v i) - Real.log (w j + t * v j))
      (logDifferential w v (i,j)) 0 := by
  have hi : HasDerivAt (fun t : ℝ => w i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (w i)
  have hj : HasDerivAt (fun t : ℝ => w j + t * v j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (w j)
  have hwi : w i + (0 : ℝ) * v i ≠ 0 := by simpa using (w.pos i).ne'
  have hwj : w j + (0 : ℝ) * v j ≠ 0 := by simpa using (w.pos j).ne'
  simpa [logDifferential] using (hi.log hwi).sub (hj.log hwj)

@[simp] theorem logDifferential_radial (w : Weight ι) (c : ℝ) :
    logDifferential w (fun i => c * w i) = 0 := by
  funext ij
  dsimp [logDifferential]
  field_simp [(w.pos ij.1).ne', (w.pos ij.2).ne'] <;> ring

/-- The derivative of a locally varying scale contributes only a radial term. -/
theorem logDifferential_change_lift (w : Weight ι) (v : ι → ℝ)
    (c b : ℝ) (hc : 0 < c) :
    logDifferential (PositiveMeasure.scale c hc w) (fun i => c*v i + b*w i) =
      logDifferential w v := by
  funext ij
  dsimp [logDifferential, PositiveMeasure.scale]
  field_simp [hc.ne', (w.pos ij.1).ne', (w.pos ij.2).ne'] <;> ring


/-- The full log-ratio differential loses exactly the radial direction. -/
theorem logDifferential_zero_iff_radial [Nonempty ι] (w : Weight ι) (v : ι → ℝ) :
    logDifferential w v = 0 ↔ ∃ c : ℝ, ∀ i, v i = c * w i := by
  classical
  constructor
  · intro h
    let j : ι := Classical.choice inferInstance
    refine ⟨v j / w j, ?_⟩
    intro i
    have hi : v i / w i - v j / w j = 0 := congrFun h (i,j)
    exact (div_eq_iff (w.pos i).ne').mp (sub_eq_zero.mp hi)
  · rintro ⟨c,hc⟩
    have hv : v = fun i => c*w i := funext hc
    rw [hv, logDifferential_radial]

section Fisher
variable [Fintype ι] [Nonempty ι]

/-- Fisher energy in homogeneous coordinates, with normalization derived from the ray. -/
def fisherEnergy (w : Weight ι) (v : ι → ℝ) : ℝ :=
  ∑ i, PositiveMeasure.normalize w i *
    (v i / w i - mean w (fun j => v j / w j))^2

theorem fisherEnergy_nonneg (w : Weight ι) (v : ι → ℝ) : 0 ≤ fisherEnergy w v :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg ((PositiveMeasure.normalize w).pos i).le (sq_nonneg _)

/-- Finite Fisher energy also descends under a locally varying homogeneous scale. -/
theorem fisherEnergy_change_lift (w : Weight ι) (v : ι → ℝ)
    (c b : ℝ) (hc : 0 < c) :
    fisherEnergy (PositiveMeasure.scale c hc w) (fun i => c*v i+b*w i) =
      fisherEnergy w v := by
  have hr : (fun i => (c*v i+b*w i) / PositiveMeasure.scale c hc w i) =
      fun i => v i / w i + b/c := by
    funext i
    change (c*v i+b*w i)/(c*w i) = v i/w i+b/c
    field_simp [hc.ne', (w.pos i).ne'] <;> ring
  have hm : mean w (fun i => v i / w i + b/c) =
      mean w (fun i => v i / w i) + b/c := by
    change rayMean (ray w) (fun i => v i / w i + b/c) =
      rayMean (ray w) (fun i => v i / w i) + b/c
    rw [rayMean_add, rayMean_const]
  unfold fisherEnergy
  change (∑ i, PositiveMeasure.normalize (PositiveMeasure.scale c hc w) i *
    ((fun j => (c*v j+b*w j) / PositiveMeasure.scale c hc w j) i -
      mean (PositiveMeasure.scale c hc w)
        (fun j => (c*v j+b*w j) / PositiveMeasure.scale c hc w j))^2) = _
  rw [hr, PositiveMeasure.normalize_scale, mean_scale, hm]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Fisher degeneracy is proved to be scale gauge, not geometric curvature. -/
theorem fisherEnergy_zero_iff_radial (w : Weight ι) (v : ι → ℝ) :
    fisherEnergy w v = 0 ↔ ∃ c : ℝ, ∀ i, v i = c * w i := by
  constructor
  · intro h
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ)
      (f := fun i => PositiveMeasure.normalize w i *
        (v i / w i - mean w (fun j => v j / w j))^2)
      (fun i _ => mul_nonneg ((PositiveMeasure.normalize w).pos i).le (sq_nonneg _))).mp h
    refine ⟨mean w (fun j => v j / w j), ?_⟩
    intro i
    have hz := (mul_eq_zero.mp (hterms i (Finset.mem_univ i))).resolve_left
      ((PositiveMeasure.normalize w).pos i).ne'
    have he : v i / w i = mean w (fun j => v j / w j) := by nlinarith
    exact (div_eq_iff (w.pos i).ne').mp he
  · rintro ⟨c,hc⟩
    have hratio : (fun i => v i / w i) = fun _ => c := by
      funext i
      rw [hc i]
      field_simp [(w.pos i).ne'] <;> ring
    have hm : mean w (fun _ => c) = c := rayMean_const (ray w) c
    change (∑ i, PositiveMeasure.normalize w i *
      ((fun j => v j / w j) i - mean w (fun j => v j / w j))^2) = 0
    rw [hratio, hm]
    simp

theorem fisherEnergy_zero_iff_logDifferential_zero (w : Weight ι) (v : ι → ℝ) :
    fisherEnergy w v = 0 ↔ logDifferential w v = 0 := by
  rw [fisherEnergy_zero_iff_radial, logDifferential_zero_iff_radial]

/-- The finite covariance formula, including its exact null directions. -/
theorem fisherEnergy_covariance (w : Weight ι) (f : ι → ℝ) :
    fisherEnergy w (fun i => w i * f i) =
      (∑ i, PositiveMeasure.normalize w i * (f i)^2) -
        (∑ i, PositiveMeasure.normalize w i * f i)^2 := by
  have hratio : (fun i => (w i*f i)/w i) = f := by
    funext i
    field_simp [(w.pos i).ne'] <;> ring
  unfold fisherEnergy
  change (∑ i, PositiveMeasure.normalize w i *
    ((fun j => w j*f j/w j) i - mean w (fun j => w j*f j/w j))^2) = _
  rw [hratio, mean_eq_sum]
  let p : ι → ℝ := fun i => PositiveMeasure.normalize w i
  let m : ℝ := ∑ i, p i * f i
  have hp : ∑ i, p i = 1 := PositiveMeasure.Z_normalize w
  have hpm : ∑ i, p i * m = m := by
    rw [← Finset.sum_mul, hp]
    ring
  change (∑ i, p i * (f i - m) ^ 2) =
    (∑ i, p i * f i ^ 2) - (∑ i, p i * f i) ^ 2
  simp_rw [sub_sq]
  simp only [mul_sub, mul_add]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmid : (∑ i, p i * (2 * f i * m)) =
      2 * ((∑ i, p i * f i) * m) := by
    calc
      (∑ i, p i * (2 * f i * m)) =
          ∑ i, 2 * ((p i * f i) * m) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * ∑ i, (p i * f i) * m := by
            rw [Finset.mul_sum]
      _ = 2 * ((∑ i, p i * f i) * m) := by
        rw [Finset.sum_mul]
  have hpm2 : (∑ i, p i * m ^ 2) = m ^ 2 := by
    rw [← Finset.sum_mul, hp]
    ring
  rw [hmid, hpm2]
  ring

end Fisher
end InfoGeometry.Projective.LogRatioDifferential
