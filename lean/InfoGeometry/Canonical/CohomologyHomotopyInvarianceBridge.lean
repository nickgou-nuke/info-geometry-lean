import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.CohomologyHomotopyInvarianceBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Lie Derivative of a Closed Form (d ω = 0) is Exact (L_X ω = d (ι_X ω)). -/
theorem lie_derivative_closed_is_exact
    (d iota_X : ExteriorAlgebra R V →ₗ[R] ExteriorAlgebra R V)
    (omega : ExteriorAlgebra R V) (hclosed : d omega = 0) :
    lieDerivative d iota_X omega = d (iota_X omega) := by
  dsimp [lieDerivative]
  rw [hclosed, map_zero, add_zero]

end InfoGeometry.Canonical.CohomologyHomotopyInvarianceBridge
