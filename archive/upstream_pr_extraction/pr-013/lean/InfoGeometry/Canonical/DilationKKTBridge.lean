import InfoGeometry.Canonical.OperatorProjectorMismatch

/-!
# Dilation/KKT bridge

A projector obstruction may feed a dilation/KKT readout only through an explicit
witness.  This module deliberately does not prove that every mismatch admits a
resolving dilation.
-/

namespace InfoGeometry.Canonical.DilationKKTBridge

open InfoGeometry.Canonical.OperatorProjectorMismatch

variable {V W R : Type*} [Ring R]

/-- Conditional dilation witness over a larger/lifted operator space. -/
@[rep_depth transport]
structure DilationWitness where
  pair : ProjectorPair (R := R)
  embed : V → W
  liftedOperator : W → W
  liftedDrazinProj : W → W
  liftedMPProj : W → W
  dilationGenerator : R
  pullbackCondition : Prop
  agreementOrCommute : Prop
  resolvedOrRepresentedInDilatedSpace : Prop
  resolvedOrRepresentedCertified : resolvedOrRepresentedInDilatedSpace

/-- If a dilation witness is supplied, the obstruction is represented/resolved in that witness space. -/
theorem DilationWitness.resolved_or_represented
    (D : DilationWitness (V := V) (W := W) (R := R)) :
    D.resolvedOrRepresentedInDilatedSpace :=
  D.resolvedOrRepresentedCertified

/-- Sourced dilation packet: source absence is the only generic vanishing theorem. -/
@[rep_depth transport]
structure DilationFromProjectorObstruction where
  pair : ProjectorPair (R := R)
  dilationGenerator : R
  sourcedByObstruction : Prop
  vanishes_of_no_source : ¬ sourcedByObstruction → dilationGenerator = 0

/-- Allowed theorem: no obstruction source implies the sourced dilation vanishes. -/
theorem dilation_vanishes_when_source_absent
    (D : DilationFromProjectorObstruction (R := R))
    (h : ¬ D.sourcedByObstruction) :
    D.dilationGenerator = 0 :=
  D.vanishes_of_no_source h

end InfoGeometry.Canonical.DilationKKTBridge
