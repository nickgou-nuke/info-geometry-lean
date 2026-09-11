import InfoGeometry.Canonical.AQFTOperatorSignatures
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# OperatorAlgebraReadiness

Readiness aliases for operator-algebra targets.
-/

namespace InfoGeometry.Canonical.OperatorAlgebraBridge

open InfoGeometry.Canonical.AQFTOperatorInterface

section Signatures

variable (Obs : Type*) [NonUnitalNormedRing Obs] [StarRing Obs]

/-- Canonical alias for C*-ready operator targets. -/
abbrev IsCStarLayer : Prop := IsCStarReady (Obs := Obs)

/-- Canonical alias for complete-C*-ready operator targets. -/
abbrev IsCompleteCStarLayer : Prop := IsCompleteCStarReady (Obs := Obs)

end Signatures

end InfoGeometry.Canonical.OperatorAlgebraBridge
