/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WeylZornMajoranaOperatorAction
import InfoGeometry.Canonical.SplitOctonionRightRegularBraid
import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes

/-! A concrete Zorn Majorana mode commuting with a bilinear bond and its
covariance under the simultaneously transformed spin action. -/

noncomputable section

namespace InfoGeometry.Twistor.WeylZornMajoranaZeroMode

open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.Twistor.WeylZornMajoranaOperatorAction
open InfoGeometry.Canonical.SplitOctonionRightRegularBraid
open InfoGeometry.Canonical.KitaevChainMajoranaZeroModes

/-- The first mode commutes with the bond of the other two modes. -/
theorem zornMajorana_zeroMode :
    majorana 0 * (majorana 1 * majorana 2) -
      (majorana 1 * majorana 2) * majorana 0 = 0 := by
  exact left_boundary_majorana_zero_mode (majorana 0) (majorana 1) (majorana 2)
    (majorana_anticommute (by decide)) (majorana_anticommute (by decide))

/-- Conjugating both the bond and the Majorana mode preserves the zero-mode
commutator. This does not claim that the untransformed bond is invariant. -/
theorem spin_transformed_zornMajorana_zeroMode (g : SL2C) :
    spinConjugation g (majorana 0) *
        (spinConjugation g (majorana 1) * spinConjugation g (majorana 2)) -
      (spinConjugation g (majorana 1) * spinConjugation g (majorana 2)) *
        spinConjugation g (majorana 0) = 0 := by
  simpa only [map_sub, map_mul, map_zero] using
    congrArg (spinConjugation g) zornMajorana_zeroMode

end InfoGeometry.Twistor.WeylZornMajoranaZeroMode
