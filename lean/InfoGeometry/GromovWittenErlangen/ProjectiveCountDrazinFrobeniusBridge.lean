import InfoGeometry.GromovWittenErlangen.LocalizedDrazinFrobeniusBridge
import InfoGeometry.Meta.Architecture

/-!
# Projective Count / Drazin-Frobenius Bridge

This module installs the L0/L1 correction for the GW-Drazin architecture.

The intended layer descent is:

```text
L0_Count:
  raw unnormalized count states

L1_Projective:
  projective count rays, fixed-sector ratios, divisor incidence weights

L2/L3:
  GW localization graph and Drazin regular/residue decomposition

L4/L5:
  Frobenius self-dual readout, semisimple residue blocks, entropy/rank
  calibrations elsewhere
```

The theorem-safe slogan is:

```text
Drazin localization is the algebraic regularization of singular projective
count strata.
```

No Gromov-Witten invariant, virtual localization theorem, projective quotient
construction, Atiyah-Singer theorem, or semisimplicity theorem is proved here.
The file records the explicit calibration data needed for the existing
GW/Drazin/Frobenius bridge to be read as a representation of a deeper
projective count substrate.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/-! ## L0/L1 projective count substrate -/

/--
L0/L1 projective count state space.

`Count` is the unnormalized count-state carrier.  `Weight` is the coefficient
or readout type used to record raw counts, fixed-sector weights, and divisor
incidence weights.
-/
@[rep_depth count]
structure ProjectiveCountStateSpace (Count Weight : Type*) where
  /-- Raw, unnormalized combinatorial count. -/
  rawCount : Count → Weight

  /-- Projective equivalence of count states, e.g. scale equivalence. -/
  sameProjectiveState : Count → Count → Prop

  /-- Divisor insertion/incidence weight on count states. -/
  divisorInsertionWeight : Count → Weight

  /-- Fixed-sector count weight, before operator assembly. -/
  fixedSectorWeight : Count → Weight

  /-- Law governing the transition from raw counts to projective readouts. -/
  projectiveReadoutLaw : Prop

  /-- Certificate for the projective readout law. -/
  projectiveReadoutCertificate : projectiveReadoutLaw

namespace ProjectiveCountStateSpace

variable {Count Weight : Type*}
variable (S : ProjectiveCountStateSpace Count Weight)

/-- The projective readout law is available. -/
@[rep_depth projective]
theorem projectiveReadout_valid :
    S.projectiveReadoutLaw :=
  S.projectiveReadoutCertificate

end ProjectiveCountStateSpace

/-! ## Count-to-GW/Drazin/Frobenius bridge -/

/--
Bridge from projective count states to the localized Drazin-Frobenius GW
readout.

This is the explicit architectural correction: the operator/Fredholm/Drazin
layer is a representation/readout of projective count geometry, not the origin
of that geometry.
-/
@[rep_depth projective]
structure ProjectiveCountDrazinFrobeniusBridge
    (Count Weight G T Target Coeff Algebra ModuliOperator : Type*)
    [Ring Algebra] where
  /-- L0/L1 count/projective substrate. -/
  projectiveBase :
    ProjectiveCountStateSpace Count Weight

  /-- Existing GW/Drazin/Frobenius bridge. -/
  localizedBridge :
    LocalizedDrazinFrobeniusBridge
      G T Target Coeff Algebra ModuliOperator

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
    {Count Weight G T Target Coeff Algebra ModuliOperator : Type*}
    [Ring Algebra]

variable (B :
  ProjectiveCountDrazinFrobeniusBridge
    Count Weight G T Target Coeff Algebra ModuliOperator)

/-- The underlying projective count readout law is available. -/
@[rep_depth projective]
theorem projectiveReadout_valid :
    B.projectiveBase.projectiveReadoutLaw :=
  B.projectiveBase.projectiveReadout_valid

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
The localized Drazin-Frobenius assembly remains valid, but is now explicitly
read as a projective-count representation.
-/
@[rep_depth operator]
theorem drazin_is_projective_count_readout :
    B.localizedBridge.gwDrazin.drazinLocalization.localizationAssemblyLaw ∧
      B.eulerWeight_eq_projectiveWeight_law ∧
      B.residue_governedBy_projectiveDivisor_law ∧
      B.frobenius_readout_of_projectiveCounts_law :=
  ⟨B.localizedBridge.localizationAssembly_valid,
    B.eulerWeight_eq_projectiveWeight_valid,
    B.residue_governedBy_projectiveDivisor_valid,
    B.frobenius_readout_of_projectiveCounts_valid⟩

/--
The Fredholm/moduli obstruction residue is still killed by the Drazin regular
inverse after descending from projective count data.
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
