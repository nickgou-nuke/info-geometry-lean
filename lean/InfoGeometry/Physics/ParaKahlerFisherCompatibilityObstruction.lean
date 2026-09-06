/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis
import InfoGeometry.Canonical.FinitePartitionCumulantReadback

noncomputable section

namespace InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction

open InfoGeometry.GrandCanonical
open InfoGeometry.Canonical.FinitePartitionCumulantReadback
open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
open InfoGeometry.Physics.ParaKahlerAmariSouriauSynthesis

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

theorem fisher_diagonal_eq_zero_of_nonneg
    (sys : ParaKahlerMetriplecticSystem ℝ g)
    (hnonneg : ∀ X : g, 0 ≤ sys.fisherMetric.cov X X)
    (hfixed : ∀ X : g, sys.fundamentalSymmetry X = X)
    (X : g) :
    sys.fisherMetric.cov X X = 0 := by
  let KX : g := sys.paraDatum.para.K X
  have hanti : sys.fisherMetric.cov KX KX =
      -sys.fisherMetric.cov X X := by
    calc
      sys.fisherMetric.cov KX KX = sys.paraDatum.metric KX KX := by
        symm
        rw [sys.metric_compat KX KX, hfixed KX]
      _ = -sys.paraDatum.metric X X :=
        sys.paraDatum.metric_anti_compat X X
      _ = -sys.fisherMetric.cov X X := by
        rw [sys.metric_compat X X, hfixed X]
  have hX := hnonneg X
  have hKX := hnonneg KX
  rw [hanti] at hKX
  linarith

theorem not_fisher_diagonal_pos_of_nonneg
    (sys : ParaKahlerMetriplecticSystem ℝ g)
    (hnonneg : ∀ X : g, 0 ≤ sys.fisherMetric.cov X X)
    (hfixed : ∀ X : g, sys.fundamentalSymmetry X = X)
    (X : g) :
    ¬ 0 < sys.fisherMetric.cov X X := by
  rw [fisher_diagonal_eq_zero_of_nonneg sys hnonneg hfixed X]
  exact lt_irrefl 0

theorem finite_logPartition_hessian_pos_of_generator_ne
    {α : Type*} [Fintype α] [Nonempty α]
    (K : α → ℝ) (β : ℝ) {i j : α} (hij : K i ≠ K j) :
    0 < GrandCanonical.hessian (canonicalParams K) β := by
  rw [logPartition_second_deriv_eq_variance]
  have hnonneg := GrandCanonical.variance_nonneg (canonicalParams K) β
  have hne : GrandCanonical.variance (canonicalParams K) β ≠ 0 := by
    intro hz
    have hall := GrandCanonical.variance_eq_zero_iff_energy_eq_mean
      (canonicalParams K) β |>.mp hz
    exact hij (hall i |>.trans (hall j |>.symm))
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem no_global_paraMetric_fisher_hessian_identification
    {α : Type*} [Fintype α] [Nonempty α]
    (K : α → ℝ) (β : ℝ) {i j : α} (hij : K i ≠ K j)
    (sys : ParaKahlerMetriplecticSystem ℝ g)
    (hnonneg : ∀ X : g, 0 ≤ sys.fisherMetric.cov X X)
    (hfixed : ∀ X : g, sys.fundamentalSymmetry X = X)
    (X : g)
    (hmatch : sys.fisherMetric.cov X X = GrandCanonical.hessian (canonicalParams K) β) :
    False := by
  have hz := fisher_diagonal_eq_zero_of_nonneg sys hnonneg hfixed X
  have hp := finite_logPartition_hessian_pos_of_generator_ne K β hij
  rw [← hmatch, hz] at hp
  exact (lt_irrefl 0) hp

theorem no_global_paraMetric_fisher_variance_identification
    {α : Type*} [Fintype α] [Nonempty α]
    (K : α → ℝ) (β : ℝ) {i j : α} (hij : K i ≠ K j)
    (sys : ParaKahlerMetriplecticSystem ℝ g)
    (hnonneg : ∀ X : g, 0 ≤ sys.fisherMetric.cov X X)
    (hfixed : ∀ X : g, sys.fundamentalSymmetry X = X)
    (X : g)
    (hmatch : sys.fisherMetric.cov X X = GrandCanonical.variance (canonicalParams K) β) :
    False := by
  have hz := fisher_diagonal_eq_zero_of_nonneg sys hnonneg hfixed X
  have hnonneg := GrandCanonical.variance_nonneg (canonicalParams K) β
  have hne : GrandCanonical.variance (canonicalParams K) β ≠ 0 := by
    intro hz
    have hall := GrandCanonical.variance_eq_zero_iff_energy_eq_mean
      (canonicalParams K) β |>.mp hz
    exact hij (hall i |>.trans (hall j |>.symm))
  have hp : 0 < GrandCanonical.variance (canonicalParams K) β :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [← hmatch, hz] at hp
  exact (lt_irrefl 0) hp

end InfoGeometry.Physics.ParaKahlerFisherCompatibilityObstruction
