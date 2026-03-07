import InfoGeometry.KK.KasparovCycle
import InfoGeometry.KK.CompactOperatorBridge

/-!
# InfoGeometry.KK.KasparovCompactOperator

Concrete lemmas translating abstract Kasparov compactness conditions to
Mathlib's `IsCompactOperator` predicate.
-/

open scoped InnerProductSpace

namespace InfoGeometry.KK

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

variable (X : KasparovCycle A B H)

/-- Marker that a Kasparov cycle uses Mathlib compact operators as its `K` predicate. -/
def IsMathlibCompactModel : Prop :=
  X.K = IsCompactEnd (H := H)

lemma superComm_isCompactOperator_of_even_rep
    (hModel : X.K = IsCompactEnd (H := H))
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactOperator ((KreinGradedModule.superComm (H := H) X.F (X.π a)) : H → H) := by
  have hcompact : X.K (KreinGradedModule.superComm (H := H) X.F (X.π a)) :=
    superComm_compact_of_even_rep (X := X) hπ_even a
  rw [hModel] at hcompact
  simpa [IsCompactEnd] using hcompact

lemma comm_isCompactOperator_of_mathlib_compact
    (hModel : X.K = IsCompactEnd (H := H)) (a : A) :
    IsCompactOperator ((X.F * X.π a - X.π a * X.F : H →L[ℝ] H) : H → H) := by
  have hcompact : X.K (X.F * X.π a - X.π a * X.F) := X.comm_compact a
  rw [hModel] at hcompact
  simpa [IsCompactEnd] using hcompact

end InfoGeometry.KK
