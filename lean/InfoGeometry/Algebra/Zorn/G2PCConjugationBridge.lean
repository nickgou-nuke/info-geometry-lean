/- SPDX-License-Identifier: MIT -/

import InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
import InfoGeometry.Algebra.Zorn.G2RootAutPCAlignment
import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
import InfoGeometry.Algebra.Zorn.G2RootAutPCConjugation
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import Mathlib.Data.Matrix.Basic

open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2RootAutPCAlignment
open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
open InfoGeometry.Algebra.Zorn.G2RootAutPCConjugation

namespace InfoGeometry.Algebra.Zorn.G2PCConjugationBridge

/-- The proposed conjugation of the two singleton PC words is obstructed by
    the native carrier conventions. -/
theorem not_c_conj_pcWord_short_one_eq_short_two :
    ¬ c * G2TwoSylowSubgroup.pcWord
        G2RootAutShortOneMatrix.shortOnePCExp * c⁻¹ =
      G2TwoSylowSubgroup.pcWord shortTwoPCExp := by
  simpa [G2RootAutShortOneMatrix.shortOnePCExp, shortTwoPCExp] using
    not_c_conj_pcWord_oneAt_two_eq_oneAt_zero

end InfoGeometry.Algebra.Zorn.G2PCConjugationBridge
