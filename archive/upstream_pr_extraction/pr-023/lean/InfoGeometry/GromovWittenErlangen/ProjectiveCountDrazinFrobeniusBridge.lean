import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.GromovWittenErlangen.LocalizedDrazinFrobeniusBridge
import InfoGeometry.Meta.Architecture

/-!
# Projective Count / Drazin-Frobenius Bridge

This module connects the already-present repo surfaces:

* `GWProjectiveCountCalibration`: L0/L1 unnormalized projective count substrate;
* `LocalizedDrazinFrobeniusBridge`: GW localization, Drazin split, Frobenius
  self-dual readout.

It deliberately does not introduce a parallel projective-count abstraction.
The count layer is the arithmetic `CountProfile` / `SamePositiveRay` lane
already implemented in `PrimitiveProjectiveRays`, exposed to GW through
`GWProjectiveCountCalibration`.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

/-! ## Count-to-GW/Drazin/Frobenius bridge -/

/--
Bridge from the repo-owned projective count calibration to the localized
Drazin-Frobenius GW readout.

The operator/Fredholm/Drazin layer is read as a representation/readout of the
projective count geometry, not as a replacement for it.
-/
@[rep_depth projective]
structure ProjectiveCountDrazinFrobeniusBridge
    (G T Target Coeff Algebra ModuliOperator : Type*)
    [Ring Algebra] where
  /-- Existing L0/L1 GW projective-count calibration. -/
  projectiveCounts :
    GWProjectiveCountCalibration G T Target Coeff

  /-- Existing GW/Drazin/Frobenius bridge. -/
  localizedBridge :
    LocalizedDrazinFrobeniusBridge
      G T Target Coeff Algebra ModuliOperator

  /--
  The localization packet used by the Drazin/Frobenius bridge is the same
  localization packet shadowed by the projective count calibration.
  -/
  localization_packet_eq :
    localizedBridge.gwDrazin.drazinLocalization.virtualLocalization =
      projectiveCounts.localization

  /--
  Calibration: localization Euler weights are read from projective fixed-sector
  count weights.
  -/
  eulerWeight_eq_projectiveWeight_law : Prop

  /-- Certificate for Euler/projective weight compatibility. -/
  eulerWeight_eq_projectiveWeight_certificate :
    eulerWeight_eq_projectiveWeight_law

  /--
  Calibration: Drazin singular residues are governed by degenerate/singular
  projective divisor strata.
  -/
  residue_governedBy_projectiveDivisor_law : Prop

  /-- Certificate for projective divisor/residue compatibility. -/
  residue_governedBy_projectiveDivisor_certificate :
    residue_governedBy_projectiveDivisor_law

  /--
  Calibration: the localized Frobenius self-dual readout is a finite readout of
  the projective count state space.
  -/
  frobenius_readout_of_projectiveCounts_law : Prop

  /-- Certificate for projective-count/Frobenius readout compatibility. -/
  frobenius_readout_of_projectiveCounts_certificate :
    frobenius_readout_of_projectiveCounts_law

namespace ProjectiveCountDrazinFrobeniusBridge

variable
    {G T Target Coeff Algebra ModuliOperator : Type*}
    [Ring Algebra]

variable (B :
  ProjectiveCountDrazinFrobeniusBridge
    G T Target Coeff Algebra ModuliOperator)

/-- The underlying GW-to-count shadow law is available. -/
@[rep_depth count]
theorem countShadow_holds :
    B.projectiveCounts.countShadowLaw :=
  B.projectiveCounts.countShadow_holds

/-- The Drazin bridge uses the same localization packet as the count shadow. -/
@[rep_depth projective]
theorem localization_packet_matches_projectiveCounts :
    B.localizedBridge.gwDrazin.drazinLocalization.virtualLocalization =
      B.projectiveCounts.localization :=
  B.localization_packet_eq

/-- The Euler/projective weight compatibility law is available. -/
@[rep_depth operator]
theorem eulerWeight_eq_projectiveWeight_valid :
    B.eulerWeight_eq_projectiveWeight_law :=
  B.eulerWeight_eq_projectiveWeight_certificate

/-- The projective divisor/Drazin residue compatibility law is available. -/
@[rep_depth operator]
theorem residue_governedBy_projectiveDivisor_valid :
    B.residue_governedBy_projectiveDivisor_law :=
  B.residue_governedBy_projectiveDivisor_certificate

/-- The projective-count/Frobenius readout law is available. -/
@[rep_depth operator]
theorem frobenius_readout_of_projectiveCounts_valid :
    B.frobenius_readout_of_projectiveCounts_law :=
  B.frobenius_readout_of_projectiveCounts_certificate

/--
The localized Drazin-Frobenius assembly is explicitly a projective-count
readout.
-/
@[rep_depth operator]
theorem drazin_is_projective_count_readout :
    B.projectiveCounts.countShadowLaw ∧
      B.localizedBridge.gwDrazin.drazinLocalization.localizationAssemblyLaw ∧
      B.eulerWeight_eq_projectiveWeight_law ∧
      B.residue_governedBy_projectiveDivisor_law ∧
      B.frobenius_readout_of_projectiveCounts_law :=
  ⟨B.countShadow_holds,
    B.localizedBridge.localizationAssembly_valid,
    B.eulerWeight_eq_projectiveWeight_valid,
    B.residue_governedBy_projectiveDivisor_valid,
    B.frobenius_readout_of_projectiveCounts_valid⟩

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
    B.localizedBridge.fredholmDrazin.obstructionResidue *
        B.localizedBridge.fredholmDrazin.regularInverse = 0 :=
  B.localizedBridge.obstructionResidue_mul_regularInverse

/--
Edge-level Drazin residues still vanish against their regular inverses in the
projective-count readout.
-/
@[rep_depth operator]
theorem edgeResidue_mul_regularInverse
    (e : B.localizedBridge.gwDrazin.drazinLocalization.virtualLocalization.graph.Edge) :
    B.localizedBridge.gwDrazin.edgeLocalizedDrazinResidue e *
        B.localizedBridge.gwDrazin.edgeLocalizedRegularInverse e = 0 :=
  B.localizedBridge.edgeResidue_mul_regularInverse e

/-- Frobenius compatibility of the projective-count readout. -/
@[rep_depth operator]
theorem frobenius_pairing_mul_left_eq_pairing_mul_right
    (a b c : Algebra) :
    B.localizedBridge.gwDrazin.frobeniusSemisimple.frobenius.pairing (a * b) c =
      B.localizedBridge.gwDrazin.frobeniusSemisimple.frobenius.pairing a (b * c) :=
  B.localizedBridge.frobenius_pairing_mul_left_eq_pairing_mul_right a b c

end ProjectiveCountDrazinFrobeniusBridge

end GromovWittenErlangen
end InfoGeometry
