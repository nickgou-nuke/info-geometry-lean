/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

noncomputable section

/-- Concrete finite paired-step package for the character-energy calculation. The average runs over
`stepCount + 1` paired increments, so the normalizing factor is always positive. -/
structure PairedStepKernelData where
  phaseScale : ℝ
  stepCount : ℕ
  step : Fin stepCount.succ → ℝ
  meanSq : ℝ → ℝ

namespace PairedStepKernelData

/-- Phase increment of the additive character at frequency `a` along the `k`-th paired step. -/
def phase (D : PairedStepKernelData) (a : ℝ) (k : Fin D.stepCount.succ) : ℝ :=
  D.phaseScale * a * D.step k

/-- The paired-step contribution `1 - cos θ_k`. -/
def pairedContribution (D : PairedStepKernelData) (a : ℝ) (k : Fin D.stepCount.succ) : ℝ :=
  1 - Real.cos (D.phase a k)

/-- Averaged Dirichlet energy of the character mode at frequency `a`. -/
def characterDirichletEnergy (D : PairedStepKernelData) (a : ℝ) : ℝ :=
  (1 / (D.stepCount.succ : ℝ)) * ∑ k : Fin D.stepCount.succ, D.pairedContribution a k

/-- Centered variance of the character mode, recorded through the squared modulus of its mean. -/
def centeredCharacterVariance (D : PairedStepKernelData) (a : ℝ) : ℝ :=
  1 - D.meanSq a

/-- The Rayleigh quotient formula, totalized at constant modes.  Only nonconstant modes are
included in `rayleighQuotients` below. -/
def rayleighQuotient (D : PairedStepKernelData) (a : ℝ) : ℝ :=
  if D.meanSq a < 1 then
    D.characterDirichletEnergy a / D.centeredCharacterVariance a
  else 0

/-- Rayleigh quotients indexed by character modes with positive centered variance. -/
def rayleighQuotients (D : PairedStepKernelData) : Set ℝ :=
  {q | ∃ a, D.meanSq a < 1 ∧ q = D.rayleighQuotient a}

/-- The spectral gap is the infimum over nonconstant character modes, or zero if there are none. -/
noncomputable def spectralGap (D : PairedStepKernelData) : ℝ := by
  classical
  exact if h : D.rayleighQuotients.Nonempty then sInf D.rayleighQuotients else 0

/-- The paired-step energy rewrites as the averaged `2 sin²(θ_k / 2)` sum. -/
def characterDirichletEnergyFormula (D : PairedStepKernelData) : Prop :=
  ∀ a : ℝ,
    D.characterDirichletEnergy a =
      (2 / (D.stepCount.succ : ℝ)) *
        ∑ k : Fin D.stepCount.succ, Real.sin (D.phase a k / 2) ^ 2

/-- Centering subtracts the character mean and leaves variance in the form `1 - |E ψ|²`. -/
def centeredCharacterVarianceFormula (D : PairedStepKernelData) : Prop :=
  ∀ a : ℝ, D.centeredCharacterVariance a = 1 - D.meanSq a

/-- Rayleigh-quotient upper bound encoded for every nonconstant character direction. -/
def spectralGapRayleighUpperBound (D : PairedStepKernelData) : Prop :=
  ∀ a : ℝ, D.meanSq a < 1 →
    D.spectralGap ≤ D.characterDirichletEnergy a / D.centeredCharacterVariance a

lemma pairedContribution_eq_two_sin_sq
    (D : PairedStepKernelData) (a : ℝ) (k : Fin D.stepCount.succ) :
    D.pairedContribution a k = 2 * Real.sin (D.phase a k / 2) ^ 2 := by
  unfold pairedContribution
  rw [Real.sin_sq_eq_half_sub (D.phase a k / 2)]
  have hphase : 2 * (D.phase a k / 2) = D.phase a k := by ring
  rw [hphase]
  ring

lemma pairedContribution_nonneg
    (D : PairedStepKernelData) (a : ℝ) (k : Fin D.stepCount.succ) :
    0 ≤ D.pairedContribution a k := by
  unfold pairedContribution
  nlinarith [Real.cos_le_one (D.phase a k)]

lemma characterDirichletEnergy_nonneg (D : PairedStepKernelData) (a : ℝ) :
    0 ≤ D.characterDirichletEnergy a := by
  unfold characterDirichletEnergy
  refine mul_nonneg ?_ ?_
  · positivity
  · refine Finset.sum_nonneg ?_
    intro k hk
    exact D.pairedContribution_nonneg a k

lemma rayleighQuotient_nonneg (D : PairedStepKernelData) (a : ℝ) :
    0 ≤ D.rayleighQuotient a := by
  by_cases hmean : D.meanSq a < 1
  · simp only [rayleighQuotient, if_pos hmean]
    have hvariance : 0 < D.centeredCharacterVariance a := by
      unfold centeredCharacterVariance
      linarith
    exact div_nonneg (D.characterDirichletEnergy_nonneg a) hvariance.le
  · simp [rayleighQuotient, hmean]

lemma spectralGap_nonneg (D : PairedStepKernelData) : 0 ≤ D.spectralGap := by
  classical
  by_cases h : D.rayleighQuotients.Nonempty
  · rw [spectralGap, dif_pos h]
    refine le_csInf h ?_
    intro q hq
    rcases hq with ⟨a, hmean, rfl⟩
    exact D.rayleighQuotient_nonneg a
  · simp [spectralGap, h]

lemma spectralGap_le_rayleighQuotient (D : PairedStepKernelData) {a : ℝ}
    (hmean : D.meanSq a < 1) :
    D.spectralGap ≤ D.characterDirichletEnergy a / D.centeredCharacterVariance a := by
  classical
  have hnonempty : D.rayleighQuotients.Nonempty := ⟨D.rayleighQuotient a,
    a, hmean, by simp [rayleighQuotient, hmean]⟩
  rw [spectralGap, dif_pos hnonempty]
  apply csInf_le
  · exact ⟨0, fun q hq => by
      rcases hq with ⟨b, hbmean, rfl⟩
      exact D.rayleighQuotient_nonneg b⟩
  · exact ⟨a, hmean, by simp [rayleighQuotient, hmean]⟩

end PairedStepKernelData

open PairedStepKernelData

/-- Paper label: `prop:fold-paired-step-dirichlet-character-identity`.
The paired-step energy collapses to the cosine/sine formula, centering only changes the mean, and
the resulting Rayleigh quotient gives the advertised upper bound. -/
theorem paper_fold_paired_step_dirichlet_character_identity (D : PairedStepKernelData) :
    D.characterDirichletEnergyFormula ∧ D.centeredCharacterVarianceFormula ∧
      D.spectralGapRayleighUpperBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    unfold PairedStepKernelData.characterDirichletEnergy
    simp_rw [D.pairedContribution_eq_two_sin_sq]
    rw [← Finset.mul_sum]
    ring
  · intro a
    rfl
  · intro a hmean
    exact D.spectralGap_le_rayleighQuotient hmean

end

end Omega.Folding
