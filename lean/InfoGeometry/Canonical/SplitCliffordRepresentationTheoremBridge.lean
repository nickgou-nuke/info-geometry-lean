import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Canonical.CARSpinorCliffordActionBridge
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.SpinorMixedCARBridge
import InfoGeometry.Canonical.SplitCliffordUniversalRepresentationBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordRepresentationTheoremBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.SplitCliffordUniversalRepresentationBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Theorem**: Split Clifford Operator Representation Scalar Action Identity.
    Connects the split quadratic pairing Q(u, α) = α(u) to the scalar representation action. -/
theorem split_clifford_representation_scalar_identity
    (u : U) (alpha : U →ₗ[R] R) (omega : ExteriorAlgebra R (U →ₗ[R] R)) :
    (splitPairingQuadraticForm u alpha) • omega = alpha u • omega :=
  rfl

end InfoGeometry.Canonical.SplitCliffordRepresentationTheoremBridge
