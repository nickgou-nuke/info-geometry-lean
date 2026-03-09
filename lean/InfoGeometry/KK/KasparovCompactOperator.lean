import InfoGeometry.KK.KasparovCycle
import InfoGeometry.KK.CompactOperatorBridge

/-!
# InfoGeometry.KK.KasparovCompactOperator

Concrete compact-operator consequences of the Kasparov-cycle interface.
-/

open scoped InnerProductSpace

namespace InfoGeometry.KK

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

variable (X : KasparovCycle A B H)

lemma superComm_isCompactOperator_of_even_rep
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactOperator ((KreinGradedModule.superComm (H := H) X.F (X.π a)) : H → H) := by
  simpa [IsCompactEnd] using (superComm_compact_of_even_rep (X := X) hπ_even a)

lemma comm_isCompactOperator_of_mathlib_compact
    (a : A) :
    IsCompactOperator ((X.F * X.π a - X.π a * X.F : H →L[ℝ] H) : H → H) := by
  simpa [IsCompactEnd] using (X.comm_compact a)

end InfoGeometry.KK
