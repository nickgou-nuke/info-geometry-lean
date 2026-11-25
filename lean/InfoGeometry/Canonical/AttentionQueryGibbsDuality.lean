/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AttentionQueryGeometry
import InfoGeometry.Inference.GibbsUniqueMinimizer

/-!
# Entropy variational duality for finite query attention

The existing finite Gibbs model with energy `-(β * K j q)` at temperature one
has exactly the query attention probabilities. Its free-energy decomposition
therefore identifies the query log-partition gap with finite relative entropy.
The entropy-regularized score has the unique maximizer given by query attention
among strictly positive normalized finite weights.

The real score scale `β` is explicit and unrestricted. The variational result
uses the positive simplex; no closed-simplex extended-real Fenchel conjugate is
constructed here.
-/

noncomputable section

open scoped BigOperators
open AttentionInformationGeometry
open InfoGeometry.Canonical.AttentionQueryGeometry
open InfoGeometry.Inference.FiniteGibbs

namespace InfoGeometry.Canonical.AttentionQueryGibbsDuality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : ℕ} [NeZero M]

/-- The existing finite Gibbs model instantiated by the scaled query scores. -/
def queryGibbsModel (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) :
    Model (Data := Fin M) (Theta := E) where
  energy j q := -(β * K j q)

omit [NeZero M] in
/-- The native Gibbs partition function at temperature one is the query
attention partition function. -/
theorem queryGibbs_partitionFunction_eq
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    partitionFunction (queryGibbsModel K β) q 1 =
      partitionZ (queryLogits K β q) := by
  simp [partitionFunction, queryGibbsModel, partitionZ, queryLogits]

omit [NeZero M] in
/-- The native Gibbs weights are exactly the existing query attention weights. -/
theorem queryGibbs_weight_eq
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    weight (queryGibbsModel K β) q 1 = queryWeight K β q := by
  funext j
  unfold weight
  rw [queryGibbs_partitionFunction_eq]
  simp [queryGibbsModel, queryWeight, softmaxProb, queryLogits]

omit [NeZero M] in
/-- The native free energy at temperature one is minus the query potential. -/
theorem queryGibbs_freeEnergy_eq
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    freeEnergy (queryGibbsModel K β) q 1 = -queryPotential K β q := by
  simp [freeEnergy, queryGibbs_partitionFunction_eq, queryPotential]

omit [NeZero M] in
/-- The native Gibbs objective is the negative of the sum of expected scaled
query score and Shannon entropy, using a finite real logarithmic sum. -/
theorem queryGibbs_objective_eq
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) (μ : Fin M → ℝ) :
    entropyRegularizedObjective (queryGibbsModel K β) q 1 μ =
      -(β * ∑ j, μ j * K j q - ∑ j, μ j * Real.log (μ j)) := by
  change (∑ j, μ j * -(β * K j q)) +
    1 * (∑ j, μ j * Real.log (μ j)) = _
  have hsum : (∑ j, μ j * -(β * K j q)) =
      -(β * ∑ j, μ j * K j q) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, one_mul]
  ring

/-- The query potential minus the entropy-regularized expected score is
exactly relative entropy to the query attention distribution. -/
theorem queryPotential_entropy_gap
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) (μ : Fin M → ℝ)
    (hμ_pos : ∀ j, 0 < μ j) (hμ_sum : ∑ j, μ j = 1) :
    queryPotential K β q -
        (β * ∑ j, μ j * K j q - ∑ j, μ j * Real.log (μ j)) =
      InfoGeometry.Inference.finiteRelativeEntropy μ (queryWeight K β q) := by
  have h := entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
    (queryGibbsModel K β) q (ε := 1) (by norm_num) μ hμ_pos hμ_sum
  rw [queryGibbs_objective_eq, queryGibbs_freeEnergy_eq,
    queryGibbs_weight_eq, one_mul] at h
  linarith only [h]

/-- Every strictly positive normalized law has entropy-regularized expected
score at most the query log-partition potential. -/
theorem queryPotential_variational_bound
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) (μ : Fin M → ℝ)
    (hμ_pos : ∀ j, 0 < μ j) (hμ_sum : ∑ j, μ j = 1) :
    β * ∑ j, μ j * K j q - ∑ j, μ j * Real.log (μ j) ≤
      queryPotential K β q := by
  have h := entropyRegularizedObjective_ge_freeEnergy
    (queryGibbsModel K β) q (ε := 1) (by norm_num) μ hμ_pos hμ_sum
  rw [queryGibbs_freeEnergy_eq, queryGibbs_objective_eq] at h
  linarith only [h]

/-- Equality in the positive-simplex variational bound holds exactly at the
query attention distribution. -/
theorem queryPotential_variational_eq_iff
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) (μ : Fin M → ℝ)
    (hμ_pos : ∀ j, 0 < μ j) (hμ_sum : ∑ j, μ j = 1) :
    β * ∑ j, μ j * K j q - ∑ j, μ j * Real.log (μ j) =
        queryPotential K β q ↔
      μ = queryWeight K β q := by
  have h := entropyRegularizedObjective_eq_freeEnergy_iff
    (queryGibbsModel K β) q (ε := 1) (by norm_num) μ hμ_pos hμ_sum
  rw [queryGibbs_objective_eq, queryGibbs_freeEnergy_eq,
    queryGibbs_weight_eq] at h
  simpa only [neg_inj] using h

/-- At query attention, the Massieu potential is expected scaled score plus
Shannon entropy. -/
theorem queryPotential_entropy_identity
    (K : Fin M → E →L[ℝ] ℝ) (β : ℝ) (q : E) :
    queryPotential K β q =
      β * ∑ j, queryWeight K β q j * K j q -
        ∑ j, queryWeight K β q j * Real.log (queryWeight K β q j) := by
  symm
  exact (queryPotential_variational_eq_iff K β q (queryWeight K β q)
    (fun j => softmaxProb_pos (queryLogits K β q) j)
    (softmaxProb_sum (queryLogits K β q))).mpr rfl

end InfoGeometry.Canonical.AttentionQueryGibbsDuality
