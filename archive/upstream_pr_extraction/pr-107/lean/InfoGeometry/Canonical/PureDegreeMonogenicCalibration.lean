import InfoGeometry.Canonical.SplitG2DiscreteHodgeCalibration

namespace InfoGeometry.Canonical

/-!
# Pure-degree monogenic calibration bridge

This file does not invent a new Dirac operator on the calibration carrier.
It packages the existing discrete split-`G₂` closed pair `φ, ψ` as a
pure-degree monogenic readout, where monogenicity means simultaneous vanishing
of the degree-3 and degree-4 coboundaries.
-/

/-- Compatibility alias for the existing discrete split-`G₂` Hodge calibration. -/
abbrev PureDegreeMonogenicCalibration := SplitG2DiscreteHodgeCalibration

namespace PureDegreeMonogenicCalibration

variable {K : FiniteOrientedCellComplex}

/-- The pure-degree monogenic readout is exactly the closed `φ/ψ` pair. -/
def monogenicReadout (C : PureDegreeMonogenicCalibration K) : Prop :=
  rationalCoboundary K 3 C.phi = 0 ∧
    rationalCoboundary K 4 (SplitG2DiscreteHodgeCalibration.psi C) = 0

theorem monogenicReadout_iff_closed_pair
    (C : PureDegreeMonogenicCalibration K) :
    monogenicReadout C ↔
      (rationalCoboundary K 3 C.phi = 0 ∧
        rationalCoboundary K 4 (SplitG2DiscreteHodgeCalibration.psi C) = 0) :=
  Iff.rfl

theorem calibration_closed_pair
    (C : PureDegreeMonogenicCalibration K) :
    rationalCoboundary K 3 C.phi = 0 ∧
      rationalCoboundary K 4
        (SplitG2DiscreteHodgeCalibration.psi C) = 0 :=
  SplitG2DiscreteHodgeCalibration.torsion_free_pair C

theorem monogenicReadout_of_calibration
    (C : PureDegreeMonogenicCalibration K) :
    monogenicReadout C :=
  SplitG2DiscreteHodgeCalibration.torsion_free_pair C

theorem psi_eq_star_phi
    (C : PureDegreeMonogenicCalibration K) :
    SplitG2DiscreteHodgeCalibration.psi C = C.star34 C.phi :=
  SplitG2DiscreteHodgeCalibration.psi_eq_star_phi C

theorem calibration_closed_pair_to_monogenic
    (C : PureDegreeMonogenicCalibration K) :
    monogenicReadout C :=
  C.monogenicReadout_of_calibration

end PureDegreeMonogenicCalibration

end InfoGeometry.Canonical
