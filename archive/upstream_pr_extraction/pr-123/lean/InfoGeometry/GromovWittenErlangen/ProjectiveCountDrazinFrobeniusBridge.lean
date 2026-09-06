import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.GromovWittenErlangen.LocalizedDrazinFrobeniusBridge
import InfoGeometry.Meta.Architecture

/-!
# Projective Count / Drazin-Frobenius Readout

This module connects the already-present repo surfaces:

* `GWProjectiveCountCalibration`: L0/L1 unnormalized projective count substrate;
* `LocalizedDrazinFrobeniusBridge`: GW localization, Drazin split, and
  Frobenius associativity readout.

It deliberately does not introduce a parallel projective-count abstraction.
The count layer is the arithmetic `CountProfile` / `SamePositiveRay` lane
already implemented in `PrimitiveProjectiveRays`, exposed to GW through
`GWProjectiveCountCalibration`.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

/-! ## Count-to-GW/Drazin/Frobenius readout -/

/--
Readout from the repo-owned projective count calibration to the localized
Drazin-Frobenius GW readout.

The operator/Fredholm/Drazin layer is read as a representation/readout of the
projective count geometry, not as a replacement for it.
-/
@[rep_depth projective]
structure ProjectiveCountDrazinFrobeniusBridge
    (G T Target Coeff Algebra ModuliOperator : Type*)
    [Ring Algebra] [StarRing Algebra] where
  /-- Existing L0/L1 GW projective-count calibration. -/
  projectiveCounts :
    GWProjectiveCountCalibration G T Target Coeff

  /-- Existing GW/Drazin/Frobenius bridge. -/
  localizedBridge :
    LocalizedDrazinFrobeniusBridge
      G T Target Coeff Algebra ModuliOperator

namespace ProjectiveCountDrazinFrobeniusBridge

variable
    {G T Target Coeff Algebra ModuliOperator : Type*}
    [Ring Algebra] [StarRing Algebra]

variable (B :
  ProjectiveCountDrazinFrobeniusBridge
    G T Target Coeff Algebra ModuliOperator)

/--
The normalized projective count shape is invariant under nonzero rescaling of
the raw count profile.
-/
@[rep_depth projective]
theorem normalizedShape_scale_counts
    (β c : ℝ) (hc : c ≠ 0) :
    InfoGeometry.Arithmetic.PrimitiveProjectiveRays.finiteArithmeticNormalizedRay
        (fun n => c * B.projectiveCounts.counts n)
        B.projectiveCounts.support β =
      B.projectiveCounts.normalizedShape β :=
  B.projectiveCounts.normalizedShape_scale_counts β c hc

/--
The Fredholm/moduli obstruction residue is killed by the Drazin regular
inverse in the projective-count readout.
-/
@[rep_depth operator]
theorem obstructionResidue_mul_regularInverse :
    LocalizedDrazinFrobeniusBridge.obstructionResidue B.localizedBridge *
        LocalizedDrazinFrobeniusBridge.regularInverse B.localizedBridge = 0 :=
  LocalizedDrazinFrobeniusBridge.obstructionResidue_mul_regularInverse B.localizedBridge

end ProjectiveCountDrazinFrobeniusBridge

end GromovWittenErlangen
end InfoGeometry
