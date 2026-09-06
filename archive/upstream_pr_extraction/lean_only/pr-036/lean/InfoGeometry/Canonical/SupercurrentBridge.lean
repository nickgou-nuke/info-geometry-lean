import InfoGeometry.Canonical.SouriauLieThermoKKTBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SupercurrentBridge

Odd supercurrent bridge for the super-coadjoint Souriau lane.

This file does not invent a new current model.  It packages the existing
super-coadjoint readout surface into a small covariance packet:

* supercurrent is an odd projection of the same moment map;
* the identity-balanced target keeps the odd readout paired with the stress
  readout by supertrace balance;
* the bridge stays at the level of explicit readouts, not a fixed-point
  invariance claim.
-/

namespace InfoGeometry.Canonical.SupercurrentBridge

open InfoGeometry.Canonical.SouriauLieThermoKKTBridge

universe u v w

/--
J-covariant supercurrent packet.

The packet records the odd readout and the corresponding supertrace balance
for a super-coadjoint moment map.  It is intentionally phrased as covariance
data, not as a `J`-fixed invariant.
-/
@[rep_depth thermo]
structure JCovariantSupercurrentPacket
    (G Gdual Orbit : Type*) where
  superMoment : SuperCoadjointMomentMapData G Gdual Orbit
  supercurrentAt : Orbit → ℝ
  supercurrent_eq_projection :
    ∀ x : Orbit,
      supercurrentAt x =
        superMoment.supercurrentProjection (superMoment.moment x)
  supertrace_balance :
    ∀ x : Orbit,
      superMoment.stressTensorProjection (superMoment.moment x) +
        supercurrentAt x = 0

namespace JCovariantSupercurrentPacket

variable {G Gdual Orbit : Type*}
variable (P : JCovariantSupercurrentPacket G Gdual Orbit)

/-- The supercurrent is exposed as the odd projection of the super-moment. -/
@[rep_depth thermo]
theorem supercurrent_eq_odd_projection (x : Orbit) :
    P.supercurrentAt x =
      P.superMoment.supercurrentProjection (P.superMoment.moment x) :=
  P.supercurrent_eq_projection x

/-- Supertrace balance is the odd/even readout cancellation. -/
@[rep_depth thermo]
theorem supertrace_balance_at (x : Orbit) :
    P.superMoment.stressTensorProjection (P.superMoment.moment x) +
      P.supercurrentAt x = 0 :=
  P.supertrace_balance x

end JCovariantSupercurrentPacket

namespace SuperCoadjointMomentMapData

variable {G Gdual Orbit : Type*}

/--
Identity-balanced supercurrent packet.

The odd supercurrent readout is the one already owned by
`identityBalanced`; the packet packages it together with the supertrace
balance.
-/
@[rep_depth thermo]
def identityBalancedSupercurrentPacket
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ) :
    JCovariantSupercurrentPacket G Gdual Orbit where
  superMoment :=
    SuperCoadjointMomentMapData.identityBalanced
      (G := G) (Gdual := Gdual) (Orbit := Orbit)
      moment geometricTemperature pairing parityOfGenerator
      stressTensorProjection
  supercurrentAt := fun x =>
    (SuperCoadjointMomentMapData.identityBalanced
      (G := G) (Gdual := Gdual) (Orbit := Orbit)
      moment geometricTemperature pairing parityOfGenerator
      stressTensorProjection).supercurrentProjection
      ((SuperCoadjointMomentMapData.identityBalanced
        (G := G) (Gdual := Gdual) (Orbit := Orbit)
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection).moment x)
  supercurrent_eq_projection := by
    intro x
    rfl
  supertrace_balance := by
    intro x
    simpa [SuperCoadjointMomentMapData.identityBalanced] using
      (SuperCoadjointMomentMapData.identityBalanced_supertrace_balance
        (G := G) (Gdual := Gdual) (Orbit := Orbit)
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection x)

/-- The identity-balanced packet exposes the odd readout theorem directly. -/
@[rep_depth thermo]
theorem identityBalanced_supercurrent_eq_projection
    (moment : Orbit → Gdual)
    (geometricTemperature : G)
    (pairing : G → Gdual → ℝ)
    (parityOfGenerator : G → SuperParity)
    (stressTensorProjection : Gdual → ℝ)
    (x : Orbit) :
    (identityBalancedSupercurrentPacket
      (G := G) (Gdual := Gdual) (Orbit := Orbit)
      moment geometricTemperature pairing parityOfGenerator
      stressTensorProjection).supercurrentAt x =
      (identityBalancedSupercurrentPacket
        (G := G) (Gdual := Gdual) (Orbit := Orbit)
        moment geometricTemperature pairing parityOfGenerator
        stressTensorProjection).superMoment.supercurrentProjection
        ((identityBalancedSupercurrentPacket
          (G := G) (Gdual := Gdual) (Orbit := Orbit)
          moment geometricTemperature pairing parityOfGenerator
          stressTensorProjection).superMoment.moment x) := by
  rfl

end SuperCoadjointMomentMapData

end InfoGeometry.Canonical.SupercurrentBridge
