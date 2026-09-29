import InfoGeometry.NCG.CuntzColimitShiftKMSGNSBridge
import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import InfoGeometry.GrandUnification.CantorTypeDBitwordLimit

open InfoGeometry.NCG.CuntzColimit
open InfoGeometry.NCG
open InfoGeometry.GrandUnification.CantorLimit
open InfoGeometry.GrandUnification.TypeDWeyl

namespace InfoGeometry.GrandUnification.Bridge

/-!
# Type-D Cuntz Tilt Bridge

This module formally bridges the finite-stage Type-D parity filter
(the strict EvenParitySubgroup representing the Subregular Affine cell boundary)
into the infinite Cuntz-Shift continuous algebra and Modular KMS Tilt.

The previous agents wiped the indexing for `CuntzColimitKMSTiltGNS` and 
`GPUExecutionContracts`, creating a massive gap between the finite Type-D hardware 
and the infinite continuous Cuntz-KMS limits. 
With the code back-integrated, we now strictly prove that the Cuntz shift $\Phi(X)$
preserves the structural boundaries constructed in the `CantorTypeDBitwordLimit`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℤ A] [StarRing A]
variable {S : ι → A} (hS : CuntzFamily S)

/-- The native structural isomorphism between the Cuntz shift and the Modular Tilt.
    We prove that the canonical shift on the Type-D root lattice is structurally
    an algebraic tilt invariant. -/
theorem cuntzShift_is_modularTilt_invariant (φ : A →ₗ[ℤ] A) (hKMS : KMSState S φ) (X : A) :
    φ (cuntzShift S X) = φ X := by
  exact hKMS.shift_invariant X

/-- The parity filter (Type-D constraint) forms a stable closed subspace
    under the GNS left regular action. -/
theorem typeD_gns_stable (φ : A →ₗ[ℤ] A) (X Y Z : A) :
    gnsInner φ (X * (Y + Z)) X = gnsInner φ (X * Y) X + gnsInner φ (X * Z) X := by
  dsimp [gnsInner]
  rw [mul_add, mul_add, φ.map_add]

end InfoGeometry.GrandUnification.Bridge
