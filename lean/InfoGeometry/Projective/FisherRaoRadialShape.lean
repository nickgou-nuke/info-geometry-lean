/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.LogRatioDifferential
import InfoGeometry.Canonical.FiniteFisherRaoSquareRoot
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Fisher--Rao mass and projective shape

This bridge uses the existing positive-measure and strictly positive
probability carriers.  It proves the actual differential of normalization,
its radial kernel, and the orthogonal decomposition of the finite Fisher
pairing into total-mass and normalized-shape contributions.  The normalized
pairing is identified with the existing projective score-variance energy.

The square-root linear map already owned by `FiniteFisherRaoSquareRoot` is
identified with the actual Frechet derivative and composed with normalization.
The orthogonality concerns constant-mass tangents.  No identification with
Shannon-entropy leaves, determinant leaves, or an infinite-dimensional
diffeomorphism quotient is asserted.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Projective.FisherRaoRadialShape

open InfoGeometry.PositiveMeasure
open InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The existing normalized positive measure in the existing simplex carrier. -/
def normalizedProbability (w : PositiveMeasure ι ℝ) : StrictProbability ι where
  probability := (normalize w).mass
  probability_pos := (normalize w).pos
  sum_probability := Z_normalize w

@[simp]
theorem normalizedProbability_apply (w : PositiveMeasure ι ℝ) (i : ι) :
    (normalizedProbability w).probability i = w i / Z w := rfl

/-- The differential of total mass on the ambient finite coordinate space. -/
def totalMassDifferential : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

omit [Nonempty ι] in
@[simp]
theorem totalMassDifferential_apply (v : ι → ℝ) :
    totalMassDifferential v = ∑ i, v i := by
  simp [totalMassDifferential]

/-- A native continuous linear map for the derivative of normalization. -/
def normalizationDifferential (w : PositiveMeasure ι ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (Z w)⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ) +
    ((-((Z w) ^ 2)⁻¹) • totalMassDifferential).smulRight w.mass

theorem normalizationDifferential_apply
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) (i : ι) :
    normalizationDifferential w v i =
      (v i - ((∑ j, v j) / Z w) * w i) / Z w := by
  change (Z w)⁻¹ * v i +
      (-((Z w) ^ 2)⁻¹ * totalMassDifferential v) * w i = _
  rw [totalMassDifferential_apply]
  generalize hM : Z w = M
  have hM0 : M ≠ 0 := hM ▸ Z_ne_zero w
  field_simp [hM0]
  ring

/-- Normalization has the stated actual Frechet derivative at every positive
finite measure.  The ambient function is defined on all coordinate vectors;
the nonzero denominator at the base point is proved from positivity. -/
theorem hasFDerivAt_normalization (w : PositiveMeasure ι ℝ) :
    HasFDerivAt (fun x : ι → ℝ => fun i => x i / ∑ j, x j)
      (normalizationDifferential w) w.mass := by
  have hmass : HasFDerivAt (fun x : ι → ℝ => ∑ i, x i)
      totalMassDifferential w.mass := by
    have hsum : (fun x : ι → ℝ => ∑ i, x i) = totalMassDifferential := by
      funext x
      exact (totalMassDifferential_apply x).symm
    rw [hsum]
    exact (totalMassDifferential (ι := ι)).hasFDerivAt
  have hinv := (hasDerivAt_inv (Z_ne_zero w)).comp_hasFDerivAt w.mass hmass
  have h := hinv.smul (hasFDerivAt_id w.mass)
  change HasFDerivAt (fun x : ι → ℝ => (∑ i, x i)⁻¹ • x)
    (normalizationDifferential w) w.mass at h
  have hfun : (fun x : ι → ℝ => (∑ i, x i)⁻¹ • x) =
      (fun x : ι → ℝ => fun i => x i / ∑ j, x j) := by
    funext x i
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hfun] at h
  exact h

/-- The normalization differential takes values in the mass-zero tangent
hyperplane of the probability simplex. -/
theorem normalizationDifferential_sum
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    ∑ i, normalizationDifferential w v i = 0 := by
  simp_rw [normalizationDifferential_apply]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change ((∑ i, v i) - ((∑ i, v i) / Z w) * Z w) / Z w = 0
  rw [div_mul_cancel₀ _ (Z_ne_zero w), sub_self, zero_div]

/-- A tangent vector splits into a radial vector and the lifted normalized
shape tangent, with no choice of a reference coordinate. -/
theorem tangent_radial_shape_decomposition
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    v = ((∑ i, v i) / Z w) • w.mass +
      Z w • normalizationDifferential w v := by
  funext i
  change v i = ((∑ j, v j) / Z w) * w i +
    Z w * normalizationDifferential w v i
  rw [normalizationDifferential_apply]
  generalize hM : Z w = M
  have hM0 : M ≠ 0 := hM ▸ Z_ne_zero w
  field_simp [hM0]
  ring

/-- Exactly the radial directions disappear under normalization. -/
theorem normalizationDifferential_zero_iff_radial
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    normalizationDifferential w v = 0 ↔
      ∃ c : ℝ, ∀ i, v i = c * w i := by
  constructor
  · intro hv
    refine ⟨(∑ j, v j) / Z w, ?_⟩
    intro i
    have hi : (v i - ((∑ j, v j) / Z w) * w i) / Z w = 0 := by
      simpa only [normalizationDifferential_apply, Pi.zero_apply] using
        congrFun hv i
    have hnum : v i - ((∑ j, v j) / Z w) * w i = 0 := by
      simpa only [zero_mul] using (div_eq_iff (Z_ne_zero w)).mp hi
    exact sub_eq_zero.mp hnum
  · rintro ⟨c, hc⟩
    have hsum : (∑ i, v i) = c * Z w := by
      simp_rw [hc]
      rw [← Finset.mul_sum]
      rfl
    funext i
    rw [normalizationDifferential_apply, hsum, hc i]
    change (c * w i - (c * Z w / Z w) * w i) / Z w = 0
    rw [mul_div_cancel_right₀ _ (Z_ne_zero w), sub_self, zero_div]

/-- The normalization and logarithmic-coordinate differentials remove the
same radial gauge directions. -/
theorem normalizationDifferential_zero_iff_logDifferential_zero
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    normalizationDifferential w v = 0 ↔
      LogRatioDifferential.logDifferential w v = 0 := by
  rw [normalizationDifferential_zero_iff_radial,
    LogRatioDifferential.logDifferential_zero_iff_radial]

omit [Nonempty ι] in
/-- The radial vector is Fisher-orthogonal to every constant-mass tangent. -/
theorem radial_orthogonal_to_mass_tangent
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) (hv : ∑ i, v i = 0) :
    (∑ i, w i * v i / w i) = 0 := by
  calc
    (∑ i, w i * v i / w i) = ∑ i, v i := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(w.pos i).ne']

    _ = 0 := hv

/-- In particular the lifted shape direction is orthogonal to radial mass. -/
theorem radial_orthogonal_to_normalized_tangent
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    (∑ i, w i * normalizationDifferential w v i / w i) = 0 :=
  radial_orthogonal_to_mass_tangent w (normalizationDifferential w v)
    (normalizationDifferential_sum w v)

/-- The full finite Fisher pairing splits into radial mass and normalized
shape pairings.  The full pairing is written as its finite sum, rather than
introduced as a duplicate energy or metric owner. -/
theorem fisherPair_radial_shape_decomposition
    (w : PositiveMeasure ι ℝ) (v z : ι → ℝ) :
    (∑ i, v i * z i / w i) =
      (∑ i, v i) * (∑ i, z i) / Z w +
        Z w * (normalizedProbability w).fisherPair
          (normalizationDifferential w v) (normalizationDifferential w z) := by
  have hpoint (i : ι) :
      v i * z i / w i =
        ((∑ j, v j) / Z w) * ((∑ j, z j) / Z w) * w i +
          (∑ j, v j) * normalizationDifferential w z i +
          (∑ j, z j) * normalizationDifferential w v i +
          Z w * (normalizationDifferential w v i *
            normalizationDifferential w z i / (normalizedProbability w).probability i) := by
    rw [normalizationDifferential_apply, normalizationDifferential_apply,
      normalizedProbability_apply]
    generalize hM : Z w = M
    have hM0 : M ≠ 0 := hM ▸ Z_ne_zero w
    field_simp [hM0, (w.pos i).ne']
    ring
  calc
    (∑ i, v i * z i / w i) =
        ∑ i, (((∑ j, v j) / Z w) * ((∑ j, z j) / Z w) * w i +
          (∑ j, v j) * normalizationDifferential w z i +
          (∑ j, z j) * normalizationDifferential w v i +
          Z w * (normalizationDifferential w v i *
            normalizationDifferential w z i / (normalizedProbability w).probability i)) := by
      exact Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        normalizationDifferential_sum, mul_zero, add_zero]
      change ((∑ i, v i) / Z w) * ((∑ i, z i) / Z w) * Z w +
          Z w * (normalizedProbability w).fisherPair
            (normalizationDifferential w v) (normalizationDifferential w z) = _
      generalize hM : Z w = M
      have hM0 : M ≠ 0 := hM ▸ Z_ne_zero w
      field_simp [hM0]


omit [Nonempty ι] in
/-- The score mean is the relative total-mass variation. -/
theorem mean_score_eq_mass_variation
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    ExpectationRatioMetric.mean w (fun i => v i / w i) =
      (∑ i, v i) / Z w := by
  unfold ExpectationRatioMetric.mean ExpectationRatioMetric.weightedSum
  apply congrArg (fun a : ℝ => a / Z w)
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(w.pos i).ne']


/-- The normalized simplex Fisher pairing is the existing projective
score-variance energy, evaluated through the actual normalization derivative. -/
theorem normalized_fisherPair_eq_projective_fisherEnergy
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    (normalizedProbability w).fisherPair
        (normalizationDifferential w v) (normalizationDifferential w v) =
      LogRatioDifferential.fisherEnergy w v := by
  unfold StrictProbability.fisherPair LogRatioDifferential.fisherEnergy
  rw [mean_score_eq_mass_variation]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizationDifferential_apply, normalizedProbability_apply,
    PositiveMeasure.normalize_apply]
  generalize hM : Z w = M
  have hM0 : M ≠ 0 := hM ▸ Z_ne_zero w
  field_simp [hM0, (w.pos i).ne']


/-- The finite Fisher energy consists of the squared mass speed divided by
mass, plus mass times the already-owned projective Fisher energy. -/
theorem fisherEnergy_radial_shape_decomposition
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    (∑ i, (v i) ^ 2 / w i) =
      (∑ i, v i) ^ 2 / Z w + Z w * LogRatioDifferential.fisherEnergy w v := by
  simpa only [pow_two, normalized_fisherPair_eq_projective_fisherEnergy] using
    fisherPair_radial_shape_decomposition w v v

omit [Nonempty ι] in
/-- The existing square-root linear map is the actual Frechet derivative of
the ambient radius-two square-root map at a positive probability vector. -/
theorem hasFDerivAt_twoSqrt (P : StrictProbability ι) :
    HasFDerivAt (fun x : ι → ℝ => fun i => 2 * Real.sqrt (x i))
      (LinearMap.toContinuousLinearMap P.twoSqrtDifferential) P.probability := by
  apply hasFDerivAt_pi'.2
  intro i
  have hi := ((hasFDerivAt_apply i P.probability).sqrt
    (P.probability_pos i).ne').const_mul 2
  apply hi.congr_fderiv
  ext v
  change 2 * ((1 / (2 * Real.sqrt (P.probability i))) * v i) =
    v i / Real.sqrt (P.probability i)
  field_simp [(Real.sqrt_pos.2 (P.probability_pos i)).ne']


/-- The actual normalized square-root derivative factors through the actual
normalization differential and the existing simplex square-root differential. -/
theorem hasFDerivAt_normalizedTwoSqrt (w : PositiveMeasure ι ℝ) :
    HasFDerivAt
      (fun x : ι → ℝ => fun i => 2 * Real.sqrt (x i / ∑ j, x j))
      ((LinearMap.toContinuousLinearMap (normalizedProbability w).twoSqrtDifferential).comp
        (normalizationDifferential w)) w.mass := by
  exact (hasFDerivAt_twoSqrt (normalizedProbability w)).comp w.mass
    (hasFDerivAt_normalization w)

/-- The squared Euclidean norm of this actual differential is the existing
projective Fisher energy. -/
theorem normalizedTwoSqrt_differential_energy
    (w : PositiveMeasure ι ℝ) (v : ι → ℝ) :
    (∑ i, (((LinearMap.toContinuousLinearMap
      (normalizedProbability w).twoSqrtDifferential).comp
        (normalizationDifferential w)) v i) ^ 2) =
      LogRatioDifferential.fisherEnergy w v := by
  simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
  rw [← normalized_fisherPair_eq_projective_fisherEnergy]
  simpa only [StrictProbability.euclideanPair, pow_two] using
    (normalizedProbability w).euclideanPair_twoSqrtDifferential
      (normalizationDifferential w v) (normalizationDifferential w v)

end InfoGeometry.Projective.FisherRaoRadialShape
