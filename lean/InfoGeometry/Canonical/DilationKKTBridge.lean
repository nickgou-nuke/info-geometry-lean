import InfoGeometry.Canonical.OperatorProjectorMismatch

/-!
# Dilation/KKT bridge

A projector obstruction may feed a dilation/KKT readout only through an explicit
witness.  This module deliberately does not prove that every mismatch admits a
resolving dilation.
-/

namespace InfoGeometry.Canonical.DilationKKTBridge

open OperatorProjectorMismatch

variable {R : Type*} [Ring R]

/-- Sourced dilation packet: source absence is the only generic vanishing theorem. -/
@[rep_depth transport]
structure DilationFromProjectorObstruction where
  pair : ProjectorPair (R := R)
  dilationGenerator : R
  sourcedByObstruction : ProjectorPair.HasProjectorAnomaly pair
  vanishes_of_no_source : ¬ ProjectorPair.HasProjectorAnomaly pair →
    dilationGenerator = 0

/-
Compatibility name for the former dilation witness.  The owner is the
projector-obstruction datum itself; unconstrained ambient maps are not evidence
of a dilation theorem.
-/
/-! Allowed theorem: no obstruction source implies the sourced dilation vanishes. -/
theorem dilation_vanishes_when_source_absent
    (D : DilationFromProjectorObstruction (R := R))
    (h : ¬ ProjectorPair.HasProjectorAnomaly D.pair) :
    D.dilationGenerator = 0 :=
  D.vanishes_of_no_source h

end InfoGeometry.Canonical.DilationKKTBridge
