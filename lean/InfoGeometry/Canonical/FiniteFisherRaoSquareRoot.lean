import Mathlib

/-!
# Finite Fisher-Rao square-root geometry

For a strictly positive finite probability vector `p`, the map

`p ↦ 2 * sqrt p`

has differential `h ↦ h / sqrt p`.  The Euclidean pairing of these
differentials is exactly the Fisher-Rao pairing.  The image lies on the
sphere of radius `2`, and tangent vectors of the probability simplex map to
vectors orthogonal to the radius.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

universe u

variable {ι : Type u} [Fintype ι]

/-- A strictly positive finite probability vector. -/
structure StrictProbability (ι : Type u) [Fintype ι] where
  probability : ι → ℝ
  probability_pos : ∀ i, 0 < probability i
  sum_probability : ∑ i : ι, probability i = 1

namespace StrictProbability

variable (P : StrictProbability ι)

/-- Tangent vectors to the affine probability hyperplane. -/
def Tangent (_P : StrictProbability ι) : Type u :=
  {h : ι → ℝ // ∑ i : ι, h i = 0}

/-- Fisher-Rao bilinear pairing. -/
def fisherPair (h k : ι → ℝ) : ℝ :=
  ∑ i : ι, h i * k i / P.probability i

/-- Ordinary Euclidean pairing on finite coordinate vectors. -/
def euclideanPair (_P : StrictProbability ι) (h k : ι → ℝ) : ℝ :=
  ∑ i : ι, h i * k i

/-- The radius-two square-root amplitude. -/
def twoSqrtAmplitude : ι → ℝ :=
  fun i => 2 * Real.sqrt (P.probability i)

/-- Differential of `p ↦ 2 sqrt p` at `P`. -/
noncomputable def twoSqrtDifferential :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun h := fun i => h i / Real.sqrt (P.probability i)
  map_add' h k := by
    funext i
    simp [add_div]
  map_smul' r h := by
    funext i
    simp [smul_eq_mul, mul_div_assoc]

@[simp] theorem twoSqrtAmplitude_apply (i : ι) :
    P.twoSqrtAmplitude i = 2 * Real.sqrt (P.probability i) :=
  rfl

@[simp] theorem twoSqrtDifferential_apply (h : ι → ℝ) (i : ι) :
    P.twoSqrtDifferential h i = h i / Real.sqrt (P.probability i) :=
  rfl

/-- The square-root amplitude lies on the sphere of radius `2`. -/
theorem twoSqrtAmplitude_normSq :
    ∑ i : ι, (P.twoSqrtAmplitude i) ^ 2 = 4 := by
  classical
  calc
    (∑ i : ι, (P.twoSqrtAmplitude i) ^ 2) =
        ∑ i : ι, 4 * P.probability i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [twoSqrtAmplitude_apply]
          rw [show (2 * Real.sqrt (P.probability i)) ^ 2 =
              4 * (Real.sqrt (P.probability i)) ^ 2 by ring]
          rw [Real.sq_sqrt (P.probability_pos i).le]
    _ = 4 * ∑ i : ι, P.probability i := by
          rw [Finset.mul_sum]
    _ = 4 := by
          rw [P.sum_probability]
          ring

/-- The differential realizes the Fisher-Rao metric in Euclidean coordinates. -/
theorem euclideanPair_twoSqrtDifferential
    (h k : ι → ℝ) :
    P.euclideanPair (P.twoSqrtDifferential h) (P.twoSqrtDifferential k) =
      P.fisherPair h k := by
  classical
  unfold euclideanPair fisherPair
  apply Finset.sum_congr rfl
  intro i hi
  rw [twoSqrtDifferential_apply, twoSqrtDifferential_apply]
  calc
    (h i / Real.sqrt (P.probability i)) *
        (k i / Real.sqrt (P.probability i)) =
      (h i * k i) /
        (Real.sqrt (P.probability i) * Real.sqrt (P.probability i)) := by
          ring
    _ = h i * k i / P.probability i := by
          rw [Real.mul_self_sqrt (P.probability_pos i).le]

/-- The Fisher-Rao quadratic form is nonnegative. -/
theorem fisherPair_self_nonnegative (h : ι → ℝ) :
    0 ≤ P.fisherPair h h := by
  unfold fisherPair
  exact Finset.sum_nonneg fun i hi =>
    div_nonneg (mul_self_nonneg (h i)) (P.probability_pos i).le

/-- A simplex tangent vector maps to a Euclidean tangent vector to the sphere. -/
theorem amplitude_orthogonal_differential (h : P.Tangent) :
    P.euclideanPair P.twoSqrtAmplitude (P.twoSqrtDifferential h.1) = 0 := by
  classical
  unfold euclideanPair
  have hpoint (i : ι) :
      P.twoSqrtAmplitude i * P.twoSqrtDifferential h.1 i = 2 * h.1 i := by
    rw [twoSqrtAmplitude_apply, twoSqrtDifferential_apply]
    have hsqrt : Real.sqrt (P.probability i) ≠ 0 :=
      (Real.sqrt_ne_zero').2 (P.probability_pos i)
    field_simp [hsqrt] <;> ring
  simp_rw [hpoint]
  rw [← Finset.mul_sum, h.2]
  ring

/-- The unscaled square-root amplitude lies on the unit sphere. -/
theorem sqrtAmplitude_normSq :
    ∑ i : ι, (Real.sqrt (P.probability i)) ^ 2 = 1 := by
  classical
  calc
    (∑ i : ι, (Real.sqrt (P.probability i)) ^ 2) =
        ∑ i : ι, P.probability i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Real.sq_sqrt (P.probability_pos i).le]
    _ = 1 := P.sum_probability

end StrictProbability

end InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

end noncomputable section
