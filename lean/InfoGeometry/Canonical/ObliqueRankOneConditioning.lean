/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Rank-one projection conditioning

The finite oblique-projection examples show that unit-length basis vectors do
not control their biorthogonal functionals when the angle degenerates. This
owner records the general norm estimate that supplies the missing condition:
a uniform bound on rank-one projection norms, together with a lower bound on
the generating vector norms, bounds the associated functionals.

The theorem does not assert basis completeness or a Markushevich basis theorem.
Those require separate hypotheses and constructions.
-/

namespace InfoGeometry.Canonical.ObliqueRankOneConditioning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rank-one operator determined by a functional and a vector. -/
def rankOne (φ : StrongDual ℝ E) (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.smulRight φ v

/-- The operator norm of a rank-one map is the product of the two factor norms. -/
theorem norm_rankOne (φ : StrongDual ℝ E) (v : E) :
    ‖rankOne φ v‖ = ‖φ‖ * ‖v‖ := by
  exact ContinuousLinearMap.norm_smulRight_apply φ v

/-- Biorthogonality makes the rank-one map an idempotent projection. -/
theorem rankOne_idempotent_of_biorthogonal
    (φ : StrongDual ℝ E) (v : E) (h : φ v = 1) :
    (rankOne φ v) * (rankOne φ v) = rankOne φ v := by
  ext x
  simp [rankOne, ContinuousLinearMap.smulRight_apply, h]

/-- A lower bound on the vector norm and an upper bound on its rank-one
projection give an upper bound on the associated functional norm. -/
theorem dualNorm_le_of_rankOne_norm_le
    (φ : StrongDual ℝ E) (v : E) (δ K : ℝ)
    (hδ : 0 < δ) (hv : δ ≤ ‖v‖)
    (hP : ‖rankOne φ v‖ ≤ K) :
    ‖φ‖ ≤ K / δ := by
  apply (le_div_iff₀ hδ).2
  calc
    ‖φ‖ * δ ≤ ‖φ‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg φ)
    _ = ‖rankOne φ v‖ := (norm_rankOne φ v).symm
    _ ≤ K := hP

/-- For a biorthogonal rank-one family, bounded projection norms and a
uniform lower bound on the vectors yield a uniform bound on the dual family. -/
theorem dualNorm_le_of_biorthogonal_rankOne_family
    {ι : Type*} (φ : ι → StrongDual ℝ E) (v : ι → E) (δ K : ℝ)
    (hδ : 0 < δ) (hv : ∀ i, δ ≤ ‖v i‖)
    (hbiorth : ∀ i, φ i (v i) = 1)
    (hP : ∀ i, ‖rankOne (φ i) (v i)‖ ≤ K) :
    ∀ i, (rankOne (φ i) (v i)) * (rankOne (φ i) (v i)) =
      rankOne (φ i) (v i) ∧ ‖φ i‖ ≤ K / δ := by
  intro i
  exact ⟨rankOne_idempotent_of_biorthogonal (φ i) (v i) (hbiorth i),
    dualNorm_le_of_rankOne_norm_le (φ i) (v i) δ K hδ (hv i) (hP i)⟩

/-- If the generating vectors have norms uniformly bounded above and away
from zero, a family of rank-one operators is uniformly bounded exactly when
its defining functionals are uniformly bounded. The lower norm bound controls
the forward implication; the upper norm bound controls the converse. -/
theorem rankOne_family_uniform_bound_iff_functional_uniform_bound
    {ι : Type*} (φ : ι → StrongDual ℝ E) (v : ι → E) (δ M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hvLower : ∀ i, δ ≤ ‖v i‖) (hvUpper : ∀ i, ‖v i‖ ≤ M) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ i, ‖rankOne (φ i) (v i)‖ ≤ K) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖φ i‖ ≤ C := by
  constructor
  · rintro ⟨K, hK, hRank⟩
    refine ⟨K / δ, div_nonneg hK (le_of_lt hδ), ?_⟩
    intro i
    exact dualNorm_le_of_rankOne_norm_le (φ i) (v i) δ K hδ
      (hvLower i) (hRank i)
  · rintro ⟨C, hC, hFunctional⟩
    refine ⟨C * M, mul_nonneg hC hM, ?_⟩
    intro i
    rw [norm_rankOne]
    calc
      ‖φ i‖ * ‖v i‖ ≤ C * ‖v i‖ :=
        mul_le_mul_of_nonneg_right (hFunctional i) (norm_nonneg _)
      _ ≤ C * M := mul_le_mul_of_nonneg_left (hvUpper i) hC

/-- Biorthogonality itself forces the product of the two norms to be at least
one; it does not provide the uniform upper bound proved above. -/
theorem one_le_norm_mul_norm_of_biorthogonal
    (φ : StrongDual ℝ E) (v : E) (h : φ v = 1) :
    1 ≤ ‖φ‖ * ‖v‖ := by
  calc
    1 = ‖(1 : ℝ)‖ := by norm_num
    _ = ‖φ v‖ := by rw [h]
    _ ≤ ‖φ‖ * ‖v‖ := φ.le_opNorm v

end InfoGeometry.Canonical.ObliqueRankOneConditioning
