import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native finite Clifford tensor tower

The finite tower is owned by `SplitCliffordTensorBridge` and
`SplitCliffordDirectLimit`.
This module deliberately does not introduce a second Clifford-algebra record or
postulat3 a Bott isomorphism.  Its stages are native `CliffordAlgebra` stages
and its connecting maps are the native graded tensor embeddings.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

abbrev CliffordTowerStage (n : ℕ) : Type := SplitClNNAlg n

/-- The native one-step connecting map of the real binary tensor tower. -/
noncomputable def cliffordTowerEmbedding (n : ℕ) :
    CliffordTowerStage n →ₐ[ℝ] CliffordTowerStage (n + 1) :=
  splitCliffordStep n

theorem cliffordTowerEmbedding_injective (n : ℕ) :
    Function.Injective (cliffordTowerEmbedding n) :=
  splitCliffordStep_injective n

/-- The composite of the native connecting maps from stage `1` to stage `5`.

This is a concrete finite-stage factorization, not a universal statement about
arbitrary user-supplied Clifford-algebra carriers.
-/
noncomputable def cliffordTowerEmbeddingToFive :
    CliffordTowerStage 1 →ₐ[ℝ] CliffordTowerStage 5 :=
  (splitCliffordStep 4).comp
    ((splitCliffordStep 3).comp
      ((splitCliffordStep 2).comp (splitCliffordStep 1)))

theorem cliffordTowerEmbeddingToFive_injective :
    Function.Injective cliffordTowerEmbeddingToFive := by
  intro x y h
  apply cliffordTowerEmbedding_injective 1
  apply cliffordTowerEmbedding_injective 2
  apply cliffordTowerEmbedding_injective 3
  apply cliffordTowerEmbedding_injective 4
  exact h

theorem clifford_tower_factors_through_five :
    ∃ f : CliffordTowerStage 1 →ₐ[ℝ] CliffordTowerStage 5,
      Function.Injective f :=
  ⟨cliffordTowerEmbeddingToFive, cliffordTowerEmbeddingToFive_injective⟩

end InfoGeometry.Canonical
