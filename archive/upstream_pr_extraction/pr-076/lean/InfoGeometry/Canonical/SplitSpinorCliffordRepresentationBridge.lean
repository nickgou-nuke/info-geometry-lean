import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.SplitSpinorCliffordRepresentationBridge

Canonical Split Quadratic Evaluation Pairing Formalized.

This module proves the scalar pairing evaluation formula `Q(u, α) = α(u)`
for the doubled vector space `E = U × Dual(U)` and its scalar multiplication identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinorCliffordRepresentationBridge

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Paired Split Vector Space E = U × Dual(U). -/
def SplitPairedSpace (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] :=
  U × (U →ₗ[R] R)

/-- **Definition**: Canonical Split Quadratic Form Q(u, α) = α(u). -/
def splitQuadraticForm (x : SplitPairedSpace R U) : R :=
  x.2 x.1

/-- **Theorem**: Canonical split quadratic evaluation identity `Q(u, α) = α(u)`. -/
theorem splitQuadraticForm_apply (u : U) (alpha : U →ₗ[R] R) :
    splitQuadraticForm (u, alpha) = alpha u :=
  rfl

/-- **Theorem**: Scalar multiplication consequence of split quadratic evaluation. -/
theorem splitQuadraticForm_apply_mul (u : U) (alpha : U →ₗ[R] R) (r : R) :
    alpha u * r = (splitQuadraticForm (u, alpha)) * r :=
  rfl


end InfoGeometry.Canonical.SplitSpinorCliffordRepresentationBridge
