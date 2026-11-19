/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.InteriorStepAndRatioSignatures
import InfoGeometry.Spectrometry.LogInteractionAndGauge

/-!
# Differential interaction and common spatial projection have different energies

The perturbation rows are `(a+b)*s`
and `(a-b)*s`. Their actual double-centered log interaction is
`±b*(s-mean s)`. Their common column mean is `a*s`; its spatial residual uses
the existing equal-weight affine fit at positions 2 through 8.

Both reported energies count both rows. The common spatial energy therefore
contains a factor of two, just as the interaction energy does. The two energies
apply different projections to `s`, so their ratio is not determined by `a/b`
alone. These are exact unweighted squared norms, not chi-square statistics or
claims about experimental uncertainty, causes, or a universal explained fraction.
-/

namespace InfoGeometry.Spectrometry.ProjectionEnergy

open scoped BigOperators
open InteriorLogSlope InteriorStepAndRatioSignatures LogInteractionAndGauge

noncomputable section

variable {J : Type*} [Fintype J]

def sign : Fin 2 → ℝ := ![1, -1]

def perturbation (a b : ℝ) (s : J → ℝ) : Fin 2 → J → ℝ :=
  fun i j => (a + sign i * b) * s j

def centered (s : J → ℝ) : J → ℝ := fun j => s j - mean s

def sumSq (s : J → ℝ) : ℝ := ∑ j, s j ^ 2

theorem mean_scale (c : ℝ) (s : J → ℝ) :
    mean (fun j => c * s j) = c * mean s := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem perturbation_rowMean (a b : ℝ) (s : J → ℝ) (i : Fin 2) :
    rowMean (perturbation a b s) i = (a + sign i * b) * mean s := by
  exact mean_scale (a + sign i * b) s

theorem perturbation_columnMean (a b : ℝ) (s : J → ℝ) (j : J) :
    columnMean (perturbation a b s) j = a * s j := by
  norm_num [columnMean, mean, perturbation, sign, Fin.sum_univ_succ] <;> ring

theorem perturbation_grandMean (a b : ℝ) (s : J → ℝ) :
    grandMean (perturbation a b s) = a * mean s := by
  have hcol : columnMean (perturbation a b s) = fun j => a * s j := by
    funext j
    exact perturbation_columnMean a b s j
  rw [← mean_columnMean, hcol]
  exact mean_scale a s

/-- This is the existing double-centering operator applied to the raw two rows. -/
theorem perturbation_interaction (a b : ℝ) (s : J → ℝ) (i : Fin 2) (j : J) :
    interaction (perturbation a b s) i j = sign i * b * centered s j := by
  unfold interaction
  rw [perturbation_rowMean, perturbation_columnMean, perturbation_grandMean]
  unfold perturbation centered
  ring

theorem sumSq_scale (c : ℝ) (s : J → ℝ) :
    sumSq (fun j => c * s j) = c ^ 2 * sumSq s := by
  simp only [sumSq, mul_pow, Finset.mul_sum]

def interactionEnergy (a b : ℝ) (s : J → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j, interaction (perturbation a b s) i j ^ 2

theorem interactionEnergy_eq (a b : ℝ) (s : J → ℝ) :
    interactionEnergy a b s = 2 * b ^ 2 * sumSq (centered s) := by
  unfold interactionEnergy
  simp_rw [perturbation_interaction]
  rw [Fin.sum_univ_two]
  change sumSq (fun j => (sign 0 * b) * centered s j) +
      sumSq (fun j => (sign 1 * b) * centered s j) = _
  rw [sumSq_scale, sumSq_scale]
  norm_num [sign] <;> ring

theorem uniformMean_eq_mean (s : Fin 7 → ℝ) :
    weightedMean uniformWeight s = mean s := by
  simp [weightedMean, uniformWeight, mean]

/-- Linearity is proved for the actual finite affine-fit residual operator. -/
theorem fittedResidual_scale (c : ℝ) (s : Fin 7 → ℝ) (j : Fin 7) :
    fittedResidual (fun k => c * s k) j = c * fittedResidual s j := by
  simp only [fittedResidual, fittedLog, uniformMean_eq_mean, mean_scale,
    weightedSlope_mul]
  ring

def commonSpatialResidual (a : ℝ) (s : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fittedResidual (fun j => a * s j)

theorem commonSpatialResidual_eq (a : ℝ) (s : Fin 7 → ℝ) (j : Fin 7) :
    commonSpatialResidual a s j = a * (s j - fittedLog s j) := by
  exact fittedResidual_scale a s j

def commonSpatialEnergy (a : ℝ) (s : Fin 7 → ℝ) : ℝ :=
  2 * sumSq (commonSpatialResidual a s)

theorem commonSpatialEnergy_eq (a : ℝ) (s : Fin 7 → ℝ) :
    commonSpatialEnergy a s = 2 * a ^ 2 * sumSq (fittedResidual s) := by
  have hres : commonSpatialResidual a s = fun j => a * fittedResidual s j := by
    funext j
    exact fittedResidual_scale a s j
  unfold commonSpatialEnergy
  rw [hres, sumSq_scale]
  ring

/-- Centering removes only the mean of this supplied step. -/
theorem step_centered_sumSq : sumSq (centered stepAtFour) = (10 / 7 : ℝ) := by
  have hm : mean stepAtFour = (5 / 7 : ℝ) := by
    rw [← uniformMean_eq_mean]
    exact step_mean
  simp only [sumSq, centered, hm]
  norm_num [stepAtFour, Fin.sum_univ_succ]

/-- The common spatial residual also removes its fitted slope. -/
theorem step_residual_sumSq : sumSq (fittedResidual stepAtFour) = (15 / 28 : ℝ) := by
  have hstep : stepProfile 0 0 1 = stepAtFour := by
    funext j
    simp [stepProfile]
  simpa only [sumSq, hstep, one_pow, mul_one] using
    stepProfile_residual_sum_sq (0 : ℝ) 0 1

theorem step_projection_ratio :
    sumSq (fittedResidual stepAtFour) / sumSq (centered stepAtFour) = (3 / 8 : ℝ) := by
  rw [step_residual_sumSq, step_centered_sumSq]
  norm_num

/-- For this particular step, the shape correction is exactly three eighths. -/
theorem step_energy_ratio (a b : ℝ) (hb : b ≠ 0) :
    commonSpatialEnergy a stepAtFour / interactionEnergy a b stepAtFour =
      (3 / 8 : ℝ) * (a / b) ^ 2 := by
  rw [commonSpatialEnergy_eq, interactionEnergy_eq,
    step_residual_sumSq, step_centered_sumSq]
  field_simp [hb] <;> ring

/-- A centered affine shape on the same physical positions. -/
def affineShape : Fin 7 → ℝ := fun j => (position j - 5) / 3

theorem affineShape_residual_zero : fittedResidual affineShape = fun _ => 0 := by
  have hshape : affineShape = stepProfile (-5 / 3) (-1 / 3) 0 := by
    funext j
    unfold affineShape stepProfile
    ring
  funext j
  rw [hshape, stepProfile_residual_vector]
  ring

theorem affineShape_centered_sumSq : sumSq (centered affineShape) = (28 / 9 : ℝ) := by
  norm_num [sumSq, centered, mean, affineShape, position, Fin.sum_univ_succ]

theorem affineShape_commonSpatialEnergy_zero (a : ℝ) :
    commonSpatialEnergy a affineShape = 0 := by
  rw [commonSpatialEnergy_eq, affineShape_residual_zero]
  simp [sumSq]

theorem affineShape_interactionEnergy (a b : ℝ) :
    interactionEnergy a b affineShape = (56 / 9 : ℝ) * b ^ 2 := by
  rw [interactionEnergy_eq, affineShape_centered_sumSq]
  ring

/-- A perfect common affine fit can coexist with strictly positive interaction. -/
theorem affineShape_interactionEnergy_pos (a b : ℝ) (hb : b ≠ 0) :
    0 < interactionEnergy a b affineShape := by
  rw [affineShape_interactionEnergy]
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero hb)

end
end InfoGeometry.Spectrometry.ProjectionEnergy
