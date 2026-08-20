import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

/-!
# Calculus of the positive-orthant surprisal potential

This owner is the negative-log readout of the existing coordinate logarithm
owner. It stays on the concrete Euclidean positive cone; it does not identify
the quotient-valued `PositiveRay` with a smooth manifold.
-/

noncomputable section

namespace InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
open InfoGeometry.Analysis.LogVolumePathIntegral
open InfoGeometry.Analysis.LogVolumeExactDifferential
open MeasureTheory
open scoped Interval

variable {α : Type*} [Fintype α]

abbrev Chart (α : Type*) := EuclideanSpace ℝ α

def coordinateSurprisalPotential (i : α) : Chart α → ℝ :=
  fun x => -coordinateLogPotential i x

theorem hasFDerivAt_coordinateSurprisalPotential
    (i : α) {x : Chart α} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateSurprisalPotential i)
      (-((1 / x i) • coordinateCLM i)) x := by
  simpa [coordinateSurprisalPotential] using
    (hasFDerivAt_coordinateLogPotential i hx).neg

theorem coordinateSurprisalPotential_contDiffOn
    (i : α) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (coordinateSurprisalPotential i)
      (interior (InfoGeometry.Projective.positiveOrthantCone (α := α) :
        Set (Chart α))) := by
  intro x hx
  have hxi : 0 < x i :=
    (InfoGeometry.Projective.mem_interior_positiveOrthantCone_iff
      (α := α) x).mp hx i
  have hlog : ContDiffAt ℝ (⊤ : WithTop ℕ∞) Real.log (x i) :=
    (Real.contDiffAt_log).2 (ne_of_gt hxi)
  exact ((hlog.comp x ((coordinateCLM i).contDiff.contDiffAt)).neg).contDiffWithinAt

theorem integral_coordinateSurprisalRate_eq_potential_sub
    (i : α) {γ : ℝ → Chart α} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < γ t i)
    (hint : IntervalIntegrable
      (logVolumeDifferential (fun t => γ t i)) volume a b) :
    ∫ t in a..b, -logVolumeDifferential (fun t => γ t i) t =
      coordinateSurprisalPotential i (γ b) -
        coordinateSurprisalPotential i (γ a) := by
  rw [intervalIntegral.integral_neg]
  rw [integral_coordinateLogRate_eq_potential_sub i hγ hpos hint]
  simp only [coordinateSurprisalPotential]
  ring

omit [Fintype α] in
theorem coordinateSurprisalPotential_difference
    (i : α) (x y : Chart α) :
    coordinateSurprisalPotential i y - coordinateSurprisalPotential i x =
      -coordinateLogPotential i y + coordinateLogPotential i x := by
  simp [coordinateSurprisalPotential]

omit [Fintype α] in
theorem coordinateSurprisalPotential_closed_loop
    (i : α) (x y : Chart α) (hxy : y i = x i) :
    coordinateSurprisalPotential i y = coordinateSurprisalPotential i x := by
  simp [coordinateSurprisalPotential, coordinateLogPotential, hxy]

def coordinateFisherMetric (x v w : Chart α) : ℝ :=
  ∑ i, (v i * w i) / (x i) ^ 2

theorem coordinateFisherMetric_comm (x v w : Chart α) :
    coordinateFisherMetric x v w = coordinateFisherMetric x w v := by
  unfold coordinateFisherMetric
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

theorem coordinateFisherMetric_add_left (x v₁ v₂ w : Chart α) :
    coordinateFisherMetric x (v₁ + v₂) w =
      coordinateFisherMetric x v₁ w + coordinateFisherMetric x v₂ w := by
  unfold coordinateFisherMetric
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change (v₁ i + v₂ i) * w i / (x i) ^ 2 =
    v₁ i * w i / (x i) ^ 2 + v₂ i * w i / (x i) ^ 2
  ring

theorem coordinateFisherMetric_add_right (x v w₁ w₂ : Chart α) :
    coordinateFisherMetric x v (w₁ + w₂) =
      coordinateFisherMetric x v w₁ + coordinateFisherMetric x v w₂ := by
  unfold coordinateFisherMetric
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change v i * (w₁ i + w₂ i) / (x i) ^ 2 =
    v i * w₁ i / (x i) ^ 2 + v i * w₂ i / (x i) ^ 2
  ring

theorem coordinateFisherMetric_smul_left (x : Chart α) (c : ℝ)
    (v w : Chart α) :
    coordinateFisherMetric x (c • v) w =
      c * coordinateFisherMetric x v w := by
  unfold coordinateFisherMetric
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (c * v i) * w i / (x i) ^ 2 =
    c * (v i * w i / (x i) ^ 2)
  ring

theorem coordinateFisherMetric_smul_right (x : Chart α) (c : ℝ)
    (v w : Chart α) :
    coordinateFisherMetric x v (c • w) =
      c * coordinateFisherMetric x v w := by
  unfold coordinateFisherMetric
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change v i * (c * w i) / (x i) ^ 2 =
    c * (v i * w i / (x i) ^ 2)
  ring

theorem coordinateFisherMetric_nonneg (x v : Chart α) :
    0 ≤ coordinateFisherMetric x v v := by
  unfold coordinateFisherMetric
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_self_nonneg _) (sq_nonneg _)

theorem coordinateFisherMetric_pos_of_coordinate_ne_zero
    {x v : Chart α} (i : α) (hx : ∀ j, 0 < x j) (hvi : v i ≠ 0) :
    0 < coordinateFisherMetric x v v := by
  unfold coordinateFisherMetric
  apply Finset.sum_pos'
  · intro j hj
    exact div_nonneg (mul_self_nonneg _) (sq_nonneg _)
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    exact div_pos (mul_self_pos.mpr hvi) (sq_pos_of_pos (hx i))

theorem coordinateFisherMetric_pos_of_ne_zero
    {x v : Chart α} (hx : ∀ i, 0 < x i) (hv : v ≠ 0) :
    0 < coordinateFisherMetric x v v := by
  classical
  by_contra hpos
  have hzero : ∀ i, v i = 0 := by
    intro i
    by_contra hi
    exact hpos (coordinateFisherMetric_pos_of_coordinate_ne_zero i hx hi)
  apply hv
  ext i
  exact hzero i

theorem coordinateFisherMetric_eq_zero_of_zero (x : Chart α) :
    coordinateFisherMetric x 0 0 = 0 := by
  simp [coordinateFisherMetric]

end InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus

end noncomputable section
