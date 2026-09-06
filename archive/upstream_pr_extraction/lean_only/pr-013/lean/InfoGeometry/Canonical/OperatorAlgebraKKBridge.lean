import InfoGeometry.Canonical.KKFoundation

open scoped InnerProductSpace

/-!
# OperatorAlgebraKKBridge

KK compactness bridge facts used by the operator-algebra layer.
-/

namespace InfoGeometry.Canonical.OperatorAlgebraBridge

open InfoGeometry.Krein
open InfoGeometry.KK

section KkBridge

variable {A B H : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/--
In the bounded KK layer, for even algebra representation, the graded
supercommutator compactness condition reduces to the cycle's compactness axiom.
-/
theorem kk_supercomm_compact_of_even_rep
    (X : KasparovCycle A B H)
    (hπ_even : ∀ a : A, KreinGradedModule.IsEven (H := H) (X.π a))
    (a : A) :
    IsCompactEnd H (KreinGradedModule.superComm (H := H) X.F (X.π a)) := by
  exact InfoGeometry.KK.superComm_compact_of_even_rep (X := X) hπ_even a

end KkBridge

end InfoGeometry.Canonical.OperatorAlgebraBridge
