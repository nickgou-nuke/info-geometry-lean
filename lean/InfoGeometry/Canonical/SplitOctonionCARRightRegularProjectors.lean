import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.OperatorAlgebra.CARProjectors

/-!
# CAR projectors on the canonical right-regular split-octonion lift

This file is only a specialization layer: the projector and chirality laws
come from the generic associative CAR calculus.
-/

namespace InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

open InfoGeometry.OperatorAlgebra.CARProjectors

theorem rightRegularCARPair_plus_idempotent (i : Fin 3) :
    plus (rightRegularCARPair i) * plus (rightRegularCARPair i) =
      plus (rightRegularCARPair i) := by
  exact plus_idempotent (rightRegularCARPair i)

theorem rightRegularCARPair_minus_idempotent (i : Fin 3) :
    minus (rightRegularCARPair i) * minus (rightRegularCARPair i) =
      minus (rightRegularCARPair i) := by
  exact minus_idempotent (rightRegularCARPair i)

theorem rightRegularCARPair_projectors_add (i : Fin 3) :
    plus (rightRegularCARPair i) + minus (rightRegularCARPair i) = 1 := by
  exact projectors_add (rightRegularCARPair i)

theorem rightRegularCARPair_chirality_sq (i : Fin 3) :
    chirality (rightRegularCARPair i) * chirality (rightRegularCARPair i) = 1 := by
  exact chirality_sq (rightRegularCARPair i)

end InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
