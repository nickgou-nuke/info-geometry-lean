import Mathlib
import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Arithmetic.WeylGaugeCantorFockBridge

Weyl-gauge normalization bridge for the finite Cantor-Fock surface.

This file does not introduce a new operator algebra.  It packages the existing
projective Weyl-gauge normalization surface together with the finite Cantor-
Fock tilt/switch owner so the normalized transport lane is graph-visible.

No infinite CAR algebra.
No CCR algebra.
No analytic continuation.
No Hilbert-Polya/RH claim.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.WeylGaugeCantorFockBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

/--
Normalized Weyl-gauge plus Cantor-Fock bridge packet.

The Weyl surface provides the projective normalization choice.  The Cantor-
Fock surface provides the normalized finite `Cl(1,1)` atom.
-/
structure WeylGaugeCantorFockBridge (State : Type*) where
  /-- Projective Weyl-gauge normalization packet. -/
  weyl : ProjectiveWeylGaugeCalibration State

namespace WeylGaugeCantorFockBridge

variable {State : Type*}
variable (B : WeylGaugeCantorFockBridge State)

/--
The projective Weyl-gauge calibration remains scale-normalized.

This is a direct re-export of the existing Weyl owner theorem.
-/
@[bridge_target_tag]
theorem total_eq_scale_mul_shape
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    B.weyl.totalReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u =
      B.weyl.weylScaleReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u *
        B.weyl.shapeCoreReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u := by
  simpa using
    (B.weyl.total_eq_scale_mul_shape counts₁ counts₂ support u)

/--
The finite Cantor-Fock normalization surface is available as bridge data.

This does not reprove the local `Cl(1,1)` relations; it only exposes the
already-closed finite owner target as a bridge-visible packet.
-/
@[bridge_target_tag]
theorem cantorFock_owner :
    PrimeCantorTiltFockRepresentationOwnerTarget :=
  PrimeCantorTiltFockRepresentation.primeCantorTiltFockRepresentationOwnerTarget

/--
The combined Weyl-gauge and Cantor-Fock packet is bridge-visible.

This is the intended normalization bridge: the projective Weyl scale/shape
packet remains normalized while the finite Cantor-Fock atom remains closed.
-/
@[bridge_target_tag]
theorem normalizedWeylGauge_and_cantorFock
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    B.weyl.totalReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u =
        B.weyl.weylScaleReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u *
          B.weyl.shapeCoreReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u ∧
    PrimeCantorTiltFockRepresentationOwnerTarget := by
  exact ⟨B.total_eq_scale_mul_shape counts₁ counts₂ support u,
    PrimeCantorTiltFockRepresentation.primeCantorTiltFockRepresentationOwnerTarget⟩

end WeylGaugeCantorFockBridge

end InfoGeometry.Arithmetic.WeylGaugeCantorFockBridge
