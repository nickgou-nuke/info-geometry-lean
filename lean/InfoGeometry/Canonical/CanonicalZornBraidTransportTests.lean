import InfoGeometry.Canonical.CanonicalZornBraidTransport

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornBraidTransportTests

open InfoGeometry.Canonical.CanonicalZornBraidTransport
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge
open InfoGeometry.Physics.QCDFureyZornProjectorBridge
open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.B3PresentedGroup (B3 B3Gen)

example (state : CanonicalZorn) :
    (braidRepresentation (PresentedGroup.of B3Gen.sig0 : B3) :
        Module.End ℂ CanonicalZorn) state =
      state + Complex.I • zMul (upperLane (e_k 0) + lowerLane (e_k 0)) state := by
  rw [braidRepresentation_sig0_apply, canonical_Q_circular_lanes]

example (state : CanonicalZorn) :
    (braidRepresentation (PresentedGroup.of B3Gen.sig1 : B3) :
        Module.End ℂ CanonicalZorn) state =
      state + Complex.I • zMul (upperLane (e_k 1) + lowerLane (e_k 1)) state := by
  rw [braidRepresentation_sig1_apply, canonical_Q_circular_lanes]

example (braid : B3) (state : CanonicalZorn) :
    (braidRepresentation braid : Module.End ℂ CanonicalZorn)
      ((braidRepresentation braid⁻¹ : Module.End ℂ CanonicalZorn) state) = state := by
  change ((braidRepresentation braid * braidRepresentation braid⁻¹ :
    (Module.End ℂ CanonicalZorn)ˣ) : Module.End ℂ CanonicalZorn) state = state
  rw [← map_mul, mul_inv_cancel, map_one]

example (state : CanonicalZorn) :
    coordinates.symm (coordinates state) = state :=
  coordinates.symm_apply_apply state

end InfoGeometry.Canonical.CanonicalZornBraidTransportTests
