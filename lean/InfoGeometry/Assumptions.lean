import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import InfoGeometry.Assumptions.Determinant
import InfoGeometry.Assumptions.DualConnections
import InfoGeometry.Assumptions.LLN
import InfoGeometry.Assumptions.ManifoldDegree
import InfoGeometry.Assumptions.ManifoldHomology
import InfoGeometry.Projective.LogSum

/-!
# Assumptions

Explicit nonconstructive layer for legacy or not-yet-formalized claims.

The canonical publication surface (`InfoGeometry`, `InfoGeometry.Library`, and
`InfoGeometry.Canonical.*`) remains constructive and does not depend on this file.
-/

namespace InfoGeometry.Assumptions

namespace Projective

/-- Compatibility alias: constructive theorem lives in `InfoGeometry.Projective`. -/
theorem logSum_inequality
    {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ)
    (ha : ∀ i, i ∈ s → 0 < a i)
    (hb : ∀ i, i ∈ s → 0 < b i) :
    (∑ i ∈ s, a i * Real.log (a i / b i))
      ≥
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) :=
  InfoGeometry.Projective.logSum_inequality s a b ha hb

end Projective

end InfoGeometry.Assumptions
