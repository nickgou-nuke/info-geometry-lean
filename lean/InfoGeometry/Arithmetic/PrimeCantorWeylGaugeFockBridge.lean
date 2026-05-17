import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge

/-!
# InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge

Weyl-gauge normalization bridge for the prime Cantor/Fock lane.

This module does not introduce a new Clifford, CAR, or Fock theory.  It
packages the existing projective Weyl-gauge normalization packet together with
the finite Cantor tilt/switch owner and the Boolean-cube CAR bridge.

The intended reading is:

* projective Weyl normalization is fixed first;
* the normalized finite Cantor tilt/switch system supplies the local
  `Cl(1,1)` atom;
* the Boolean-cube CAR bridge preserves the finite Möbius/chirality readout.

No infinite Cantor `L²` completion.
No analytic Euler product.
No Hilbert-Polya/RH claim.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
open InfoGeometry.Arithmetic.PrimeBooleanCubeCARBridge

/--
Weyl-gauge normalization packet for the Cantor/Fock lane.

The bridge is intentionally thin: it stores the projective Weyl calibration
and the already-closed finite Cantor/Boolean bridge proofs.
-/
structure PrimeCantorWeylGaugeFockBridge
    (State : Type*) where
  /-- Projective Weyl-gauge normalization packet. -/
  weyl : ProjectiveWeylGaugeCalibration State

/--
Bridge target for the Weyl-gauge normalized Cantor/Fock lane.

This is the finite normalization statement:
projective Weyl scale/shape data are available, the finite Cantor
tilt/switch atom is closed, and the Boolean readout bridge is preserved.
-/
@[owner_target_tag]
def PrimeCantorWeylGaugeFockBridgeOwnerTarget
    (State : Type*) : Prop :=
  ∀ (B : PrimeCantorWeylGaugeFockBridge State)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ),
    B.weyl.totalReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u =
      B.weyl.weylScaleReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u *
        B.weyl.shapeCoreReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u

/-- The finite Weyl-gauge Cantor/Fock bridge target is closed. -/
theorem primeCantorWeylGaugeFockBridgeOwnerTarget
    (State : Type*) :
    PrimeCantorWeylGaugeFockBridgeOwnerTarget State := by
  intro B counts₁ counts₂ support u
  exact B.weyl.total_eq_scale_mul_shape counts₁ counts₂ support u

/--
The normalized Weyl-gauge and Cantor/Fock bridge are available simultaneously.

This is the bridge-visible version of the normalization story: the projective
Weyl packet remains normalized, the finite Cantor tilt/switch atom remains
closed, and the Boolean/CAR bridge remains preserved.
-/
@[bridge_target_tag]
theorem normalizedWeylGauge_and_cantorFock
    {State : Type*}
    (B : PrimeCantorWeylGaugeFockBridge State)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    B.weyl.totalReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u =
      B.weyl.weylScaleReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u *
        B.weyl.shapeCoreReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u ∧
    PrimeCantorTiltFockRepresentationOwnerTarget ∧
    PrimeBooleanCubeCARBridgeOwnerTarget := by
  exact ⟨B.weyl.total_eq_scale_mul_shape counts₁ counts₂ support u,
    primeCantorTiltFockRepresentationOwnerTarget,
    primeBooleanCubeCARBridgeOwnerTarget⟩

end InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge
