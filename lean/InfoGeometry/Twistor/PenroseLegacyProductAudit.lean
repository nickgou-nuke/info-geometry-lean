import InfoGeometry.Physics.PenroseQuantizedTwistorSplitOctonion
import InfoGeometry.Twistor.PenroseLiteralCrossObstruction

/-!
# Direct regression against the historical Penrose product owner

This file does not redefine the old product. It evaluates that exact public
operation on two of its real bi-twistors and disproves left alternativity.
The old positive-definite dot readout is also kept separate from the signed
Hermitian form used in the new reconstruction.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseLegacyProductAudit

open InfoGeometry.Twistor.PenroseLiteralCrossObstruction

abbrev Legacy := InfoGeometry.Physics.PenroseTwistor.BiTwistor

/-- Real bi-twistors in the historical owner's own reality convention. -/
def legacyX : Legacy := { up := testX, dn := testX }
def legacyY : Legacy := { up := testY, dn := testY }

theorem legacy_pair_is_real :
    InfoGeometry.Physics.PenroseTwistor.isRealBiTwistor legacyX ∧
      InfoGeometry.Physics.PenroseTwistor.isRealBiTwistor legacyY := by
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [legacyX, legacyY, testX, testY]

/-- This checks the exact existing product, not only a newly introduced candidate. -/
set_option maxHeartbeats 2000000 in
theorem legacy_product_not_left_alternative :
    InfoGeometry.Physics.PenroseTwistor.splitOctonionicMul legacyX
        (InfoGeometry.Physics.PenroseTwistor.splitOctonionicMul legacyX legacyY) ≠
      InfoGeometry.Physics.PenroseTwistor.splitOctonionicMul
        (InfoGeometry.Physics.PenroseTwistor.splitOctonionicMul legacyX legacyX) legacyY := by
  intro h
  have hc := congrArg (fun A : Legacy => (A.up 2).re) h
  norm_num [InfoGeometry.Physics.PenroseTwistor.splitOctonionicMul,
    InfoGeometry.Physics.PenroseTwistor.scalarPart,
    InfoGeometry.Physics.PenroseTwistor.vectorPart,
    InfoGeometry.Physics.PenroseTwistor.vectorCrossProduct,
    InfoGeometry.Physics.PenroseTwistor.penroseTripleProduct,
    InfoGeometry.Physics.PenroseTwistor.bracketCW,
    InfoGeometry.Physics.PenroseTwistor.bracketCZ,
    InfoGeometry.Physics.PenroseTwistor.twistorI,
    InfoGeometry.Physics.PenroseTwistor.twistorDot,
    InfoGeometry.Physics.PenroseTwistor.unitE,
    legacyX, legacyY, testX, testY, Fin.sum_univ_four] at hc

/-- The historical Euclidean dot and the native signed dot differ on this real input. -/
theorem legacy_dot_is_not_signed_metric :
    InfoGeometry.Physics.PenroseTwistor.twistorDot legacyY legacyY = 2 ∧
      InfoGeometry.Twistor.PenroseSignedCCRGeometry.metric testY testY = -2 := by
  constructor
  · norm_num [InfoGeometry.Physics.PenroseTwistor.twistorDot, legacyY, testY,
      Fin.sum_univ_four]
  · exact test_pair_geometry.2.1

end InfoGeometry.Twistor.PenroseLegacyProductAudit
