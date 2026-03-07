import InfoGeometry.KK.CompactLike
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# InfoGeometry.KK.CompactOperatorBridge

Concrete bridge from the abstract `CompactLike` interface to Mathlib's
`IsCompactOperator` predicate on continuous linear maps.
-/

namespace InfoGeometry.KK

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Mathlib compact-operator predicate specialized to real endomorphisms. -/
abbrev IsCompactEnd (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H →L[ℝ] H) : Prop :=
  IsCompactOperator (A : H → H)

instance instCompactLikeIsCompactEnd :
    CompactLike (Op := H →L[ℝ] H) (IsCompactEnd (H := H)) where
  zero_mem := by
    simpa [IsCompactEnd] using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  add_mem := by
    intro A B hA hB
    simpa [IsCompactEnd] using (IsCompactOperator.add hA hB)
  smul_mem := by
    intro r A hA
    simpa [IsCompactEnd] using (IsCompactOperator.smul hA r)

end InfoGeometry.KK

