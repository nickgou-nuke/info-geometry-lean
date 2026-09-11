import Mathlib.Algebra.Category.ModuleCat.Limits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-!
# Native `ModuleCat` colimit for the split Clifford tower

The split Clifford tower already satisfies Mathlib's `DirectedSystem` laws.
This module presents it through `ModuleCat.directLimitCocone` and its proved
universal property, rather than through repository-owned sequential-system or
cocone records.
-/

noncomputable section

namespace InfoGeometry.Spectral.Colimit

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit

/-- The split Clifford transition map as a Mathlib linear map. -/
abbrev splitCliffordLinearMap (m n : ℕ) (h : m ≤ n) :
    SplitClNNAlg m →ₗ[ℝ] SplitClNNAlg n :=
  (splitCliffordMap m n h).toLinearMap

/-- The linear transition maps satisfy Mathlib's directed-system laws. -/
instance splitCliffordLinearDirectedSystem :
    DirectedSystem SplitClNNAlg
      (fun m n h => splitCliffordLinearMap m n h) where
  map_self := by
    intro m x
    exact congrArg
      (fun φ : SplitClNNAlg m →ₐ[ℝ] SplitClNNAlg m => φ x)
      (splitCliffordMap_refl m)
  map_map := by
    intro k j i hij hjk x
    simpa using
      (splitCliffordMap_apply_trans i j k hij hjk x).symm

/-- The canonical Mathlib `ModuleCat` cocone of the split Clifford directed
system. -/
noncomputable abbrev SplitCliffordModuleCocone :=
  ModuleCat.directLimitCocone SplitClNNAlg
    (fun m n h => splitCliffordLinearMap m n h)

/-- The canonical split Clifford cocone satisfies the genuine colimit
universal property in `ModuleCat ℝ`. -/
noncomputable def splitCliffordModuleCoconeIsColimit :
    IsColimit SplitCliffordModuleCocone :=
  ModuleCat.directLimitIsColimit SplitClNNAlg
    (fun m n h => splitCliffordLinearMap m n h)

end InfoGeometry.Spectral.Colimit
