/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.FisherKreinLorentz
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Canonical scalar stress in an orthonormal Lorentz frame

The derivative covector has four real components. The full matrix
`lambda * (v_mu * v_nu - eta_mu_nu * eta(v,v) / 2)` is constructed using the
existing `(-,+,+,+)` Fisher-Krein metric; mixed components are retained.

`meanSpatialStress` is one third of the spatial trace. For an arbitrary
covector, or an arbitrary finite weighted sum, it is not automatically the
pressure of an isotropic perfect fluid. No angular isotropization, continuum
coarse-graining, field equation, or cosmological solution is assumed or proved.

The finite weighted identities need neither positive nor normalized weights.
Those conditions belong to a probabilistic interpretation when one is used.
-/

noncomputable section

namespace InfoGeometry.Physics.CanonicalScalarStress

open InfoGeometry.Physics.FisherKreinLorentz
open scoped BigOperators Matrix

/-- The spatial quadratic contribution of a derivative covector. -/
def spatialGradientSq (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 3, v i.succ ^ 2

/-- Contraction with the existing orthonormal Lorentz metric. -/
def derivativeContraction (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, fisherKreinLorentz4 i j * v i * v j

/-- The canonical scalar kinetic stress tensor, with every matrix entry present. -/
def stressTensor (lambda : ℝ) (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => lambda *
    (v i * v j - (1 / 2 : ℝ) * fisherKreinLorentz4 i j * derivativeContraction v)

/-- The time-time component in the selected orthonormal frame. -/
def energyDensity (lambda : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  stressTensor lambda v 0 0

/-- One third of the spatial trace; isotropy is a separate condition. -/
def meanSpatialStress (T : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (∑ i : Fin 3, T i.succ i.succ) / 3

/-- A purely temporal derivative covector. -/
def homogeneousCovector (u : ℝ) : Fin 4 → ℝ := ![u, 0, 0, 0]

/-- This fixed orthonormal metric is also its inverse. -/
theorem metric_mul_self :
    (fisherKreinLorentz4 : Matrix (Fin 4) (Fin 4) ℝ) * fisherKreinLorentz4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, fisherKreinLorentz4,
      fisherKreinReflect4, fisherUnit4, delta4, modularTimeCovector4]

private theorem metric_symmetric (i j : Fin 4) :
    fisherKreinLorentz4 i j = fisherKreinLorentz4 j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [fisherKreinLorentz4_offdiag hij, fisherKreinLorentz4_offdiag hij.symm]

theorem spatialGradientSq_nonneg (v : Fin 4 → ℝ) : 0 ≤ spatialGradientSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The metric contraction is computed from its full double sum. -/
theorem derivativeContraction_eq (v : Fin 4 → ℝ) :
    derivativeContraction v = -(v 0) ^ 2 + spatialGradientSq v := by
  simp [derivativeContraction, spatialGradientSq, Fin.sum_univ_four,
    Fin.sum_univ_three, fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4,
    delta4, modularTimeCovector4] <;> ring

/-- The full scalar stress tensor is symmetric. -/
theorem stressTensor_symmetric (lambda : ℝ) (v : Fin 4 → ℝ) (i j : Fin 4) :
    stressTensor lambda v i j = stressTensor lambda v j i := by
  unfold stressTensor
  rw [metric_symmetric i j]
  ring

/-- The mixed tensor entries retain the products of distinct covector components. -/
theorem stressTensor_offdiag (lambda : ℝ) (v : Fin 4 → ℝ)
    {i j : Fin 4} (hij : i ≠ j) :
    stressTensor lambda v i j = lambda * (v i * v j) := by
  simp [stressTensor, fisherKreinLorentz4_offdiag hij]

/-- Each spatial diagonal follows from the same full tensor definition. -/
theorem stressTensor_spatial_diag (lambda : ℝ) (v : Fin 4 → ℝ) (i : Fin 3) :
    stressTensor lambda v i.succ i.succ =
      lambda * (v i.succ ^ 2 + (v 0) ^ 2 / 2 - spatialGradientSq v / 2) := by
  rw [stressTensor, fisherKreinLorentz4_spatial_diag (Fin.succ_ne_zero i),
    derivativeContraction_eq]
  ring

theorem energyDensity_eq (lambda : ℝ) (v : Fin 4 → ℝ) :
    energyDensity lambda v = lambda / 2 * ((v 0) ^ 2 + spatialGradientSq v) := by
  rw [energyDensity, stressTensor, fisherKreinLorentz4_time_time,
    derivativeContraction_eq]
  ring

/-- Spatial trace of the canonical tensor. The temporal coefficient is `lambda / 2`. -/
theorem meanSpatialStress_stressTensor (lambda : ℝ) (v : Fin 4 → ℝ) :
    meanSpatialStress (stressTensor lambda v) =
      lambda / 2 * (v 0) ^ 2 - lambda / 6 * spatialGradientSq v := by
  unfold meanSpatialStress
  simp_rw [stressTensor_spatial_diag]
  simp [spatialGradientSq, Fin.sum_univ_three] <;> ring

theorem energyDensity_nonneg (lambda : ℝ) (v : Fin 4 → ℝ) (hlambda : 0 ≤ lambda) :
    0 ≤ energyDensity lambda v := by
  rw [energyDensity_eq]
  exact mul_nonneg (div_nonneg hlambda (by norm_num))
    (add_nonneg (sq_nonneg _) (spatialGradientSq_nonneg v))

@[simp] theorem spatialGradientSq_homogeneous (u : ℝ) :
    spatialGradientSq (homogeneousCovector u) = 0 := by
  simp [spatialGradientSq, homogeneousCovector, Fin.sum_univ_three]

@[simp] theorem energyDensity_homogeneous (lambda u : ℝ) :
    energyDensity lambda (homogeneousCovector u) = lambda / 2 * u ^ 2 := by
  rw [energyDensity_eq, spatialGradientSq_homogeneous]
  simp [homogeneousCovector]

@[simp] theorem meanSpatialStress_homogeneous (lambda u : ℝ) :
    meanSpatialStress (stressTensor lambda (homogeneousCovector u)) =
      lambda / 2 * u ^ 2 := by
  rw [meanSpatialStress_stressTensor, spatialGradientSq_homogeneous]
  simp [homogeneousCovector]

/-- Vanishing spatial derivatives give equal mean spatial stress and density. -/
theorem meanSpatialStress_eq_energyDensity_of_spatial_zero
    (lambda : ℝ) (v : Fin 4 → ℝ) (hspatial : spatialGradientSq v = 0) :
    meanSpatialStress (stressTensor lambda v) = energyDensity lambda v := by
  rw [meanSpatialStress_stressTensor, energyDensity_eq, hspatial]
  ring

/-- Equal temporal and spatial quadratic contributions give `3 p = rho`. -/
theorem three_meanSpatialStress_eq_energyDensity_of_balanced
    (lambda : ℝ) (v : Fin 4 → ℝ) (hbalance : spatialGradientSq v = (v 0) ^ 2) :
    3 * meanSpatialStress (stressTensor lambda v) = energyDensity lambda v := by
  rw [meanSpatialStress_stressTensor, energyDensity_eq, hbalance]
  ring

private theorem scaled_pressure_eq_zero_iff (lambda temporal spatial : ℝ)
    (hlambda : lambda ≠ 0) :
    lambda / 2 * temporal - lambda / 6 * spatial = 0 ↔ spatial = 3 * temporal := by
  have hfactor : lambda / 2 * temporal - lambda / 6 * spatial =
      (lambda / 6) * (3 * temporal - spatial) := by ring
  have hdiv : lambda / 6 ≠ 0 := div_ne_zero hlambda (by norm_num)
  rw [hfactor, mul_eq_zero]
  simp only [hdiv, false_or, sub_eq_zero]
  exact eq_comm

/-- The exact zero-spatial-trace criterion; it does not assert perfect-fluid isotropy. -/
theorem meanSpatialStress_eq_zero_iff (lambda : ℝ) (v : Fin 4 → ℝ)
    (hlambda : lambda ≠ 0) :
    meanSpatialStress (stressTensor lambda v) = 0 ↔
      spatialGradientSq v = 3 * (v 0) ^ 2 := by
  rw [meanSpatialStress_stressTensor]
  exact scaled_pressure_eq_zero_iff lambda ((v 0) ^ 2) (spatialGradientSq v) hlambda

/-- A nonzero homogeneous canonical field with positive coupling has positive spatial stress. -/
theorem meanSpatialStress_homogeneous_pos (lambda u : ℝ)
    (hlambda : 0 < lambda) (hu : u ≠ 0) :
    0 < meanSpatialStress (stressTensor lambda (homogeneousCovector u)) := by
  rw [meanSpatialStress_homogeneous]
  exact mul_pos (div_pos hlambda (by norm_num)) (sq_pos_of_ne_zero hu)

/-- Mixed components need not vanish, even in the fixed diagonal metric frame. -/
theorem stressTensor_mixed_example :
    stressTensor 1 ![(1 : ℝ), 1, 0, 0] 0 1 = 1 := by
  rw [stressTensor_offdiag 1 _ (by decide : (0 : Fin 4) ≠ 1)]
  norm_num

/-- The constructed tensor family also retains noncommuting matrix products.
Symmetry of each tensor does not impose commutativity between different tensors. -/
theorem stressTensor_noncommuting_examples :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ,
      A * B ≠ B * A ∧
        A = stressTensor 1 ![(1 : ℝ), 1, 0, 0] ∧
        B = stressTensor 1 ![(1 : ℝ), 0, 1, 0] := by
  refine ⟨stressTensor 1 ![(1 : ℝ), 1, 0, 0],
    stressTensor 1 ![(1 : ℝ), 0, 1, 0], ?_, rfl, rfl⟩
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 1 2) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_four, stressTensor, derivativeContraction,
    fisherKreinLorentz4, fisherKreinReflect4, fisherUnit4, delta4,
    modularTimeCovector4] at hentry

section FiniteAverage

variable {alpha : Type*}

/-- A finite weighted sum of full stress matrices. No isotropy is imposed. -/
def averagedStress (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ)
    (v : alpha → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ a ∈ s, w a • stressTensor lambda (v a)

def weightedTemporalSq (s : Finset alpha) (w : alpha → ℝ)
    (v : alpha → Fin 4 → ℝ) : ℝ :=
  ∑ a ∈ s, w a * (v a 0) ^ 2

def weightedSpatialSq (s : Finset alpha) (w : alpha → ℝ)
    (v : alpha → Fin 4 → ℝ) : ℝ :=
  ∑ a ∈ s, w a * spatialGradientSq (v a)

theorem averagedStress_apply (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ)
    (v : alpha → Fin 4 → ℝ) (i j : Fin 4) :
    averagedStress s w lambda v i j = ∑ a ∈ s, w a * stressTensor lambda (v a) i j := by
  simp [averagedStress, Matrix.sum_apply, Matrix.smul_apply]

theorem averagedStress_symmetric (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ)
    (v : alpha → Fin 4 → ℝ) (i j : Fin 4) :
    averagedStress s w lambda v i j = averagedStress s w lambda v j i := by
  rw [averagedStress_apply, averagedStress_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [stressTensor_symmetric lambda (v a) i j]

/-- Finite averaging retains mixed second moments unless further conditions make them vanish. -/
theorem averagedStress_offdiag (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ)
    (v : alpha → Fin 4 → ℝ) {i j : Fin 4} (hij : i ≠ j) :
    averagedStress s w lambda v i j = lambda * (∑ a ∈ s, w a * (v a i * v a j)) := by
  rw [averagedStress_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [stressTensor_offdiag lambda (v a) hij]
  ring

theorem averagedStress_energy (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ)
    (v : alpha → Fin 4 → ℝ) :
    averagedStress s w lambda v 0 0 =
      lambda / 2 * (weightedTemporalSq s w v + weightedSpatialSq s w v) := by
  rw [averagedStress_apply]
  change (∑ a ∈ s, w a * energyDensity lambda (v a)) = _
  calc
    _ = ∑ a ∈ s, lambda / 2 * (w a * (v a 0) ^ 2 + w a * spatialGradientSq (v a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [energyDensity_eq]
      ring
    _ = lambda / 2 * (weightedTemporalSq s w v + weightedSpatialSq s w v) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      rfl

/-- The spatial trace commutes with the constructed finite weighted sum. -/
theorem meanSpatialStress_averagedStress (s : Finset alpha) (w : alpha → ℝ)
    (lambda : ℝ) (v : alpha → Fin 4 → ℝ) :
    meanSpatialStress (averagedStress s w lambda v) =
      ∑ a ∈ s, w a * meanSpatialStress (stressTensor lambda (v a)) := by
  unfold meanSpatialStress
  simp only [averagedStress_apply]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum]
  ring

/-- The correct temporal and spatial coefficients survive finite averaging. -/
theorem averagedStress_meanSpatialStress (s : Finset alpha) (w : alpha → ℝ)
    (lambda : ℝ) (v : alpha → Fin 4 → ℝ) :
    meanSpatialStress (averagedStress s w lambda v) =
      lambda / 2 * weightedTemporalSq s w v - lambda / 6 * weightedSpatialSq s w v := by
  rw [meanSpatialStress_averagedStress]
  calc
    _ = ∑ a ∈ s,
        (lambda / 2) * (w a * (v a 0) ^ 2) -
          (lambda / 6) * (w a * spatialGradientSq (v a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [meanSpatialStress_stressTensor]
      ring
    _ = lambda / 2 * weightedTemporalSq s w v - lambda / 6 * weightedSpatialSq s w v := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl

theorem averagedStress_meanSpatialStress_eq_zero_iff
    (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ) (v : alpha → Fin 4 → ℝ)
    (hlambda : lambda ≠ 0) :
    meanSpatialStress (averagedStress s w lambda v) = 0 ↔
      weightedSpatialSq s w v = 3 * weightedTemporalSq s w v := by
  rw [averagedStress_meanSpatialStress]
  exact scaled_pressure_eq_zero_iff lambda (weightedTemporalSq s w v)
    (weightedSpatialSq s w v) hlambda

theorem three_averagedStress_meanSpatialStress_eq_energy_of_balanced
    (s : Finset alpha) (w : alpha → ℝ) (lambda : ℝ) (v : alpha → Fin 4 → ℝ)
    (hbalance : weightedSpatialSq s w v = weightedTemporalSq s w v) :
    3 * meanSpatialStress (averagedStress s w lambda v) = averagedStress s w lambda v 0 0 := by
  rw [averagedStress_meanSpatialStress, averagedStress_energy, hbalance]
  ring

end FiniteAverage

end InfoGeometry.Physics.CanonicalScalarStress

end
