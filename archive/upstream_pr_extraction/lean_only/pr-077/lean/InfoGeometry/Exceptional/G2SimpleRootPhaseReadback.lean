/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2DiagonalPhaseTable
import InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

namespace InfoGeometry.Exceptional.G2DiagonalPhase

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots
open InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign

theorem s1Root_alpha1_readback :
    s1Root (signedRootCoordinate (false, G2PositiveRoot.alpha)) =
      signedRootCoordinate (true, G2PositiveRoot.alpha) := by
  apply Subtype.ext
  change s1 alpha1 = (-1, 0)
  exact s1_alpha1_neg

theorem s2Root_alpha2_readback :
    s2Root (signedRootCoordinate (false, G2PositiveRoot.beta)) =
      signedRootCoordinate (true, G2PositiveRoot.beta) := by
  apply Subtype.ext
  change s2 alpha2 = (0, -1)
  exact s2_alpha2_neg

theorem phaseTable_s1_alpha1_transition (ζ : ℂ) :
    phaseTable ζ (s1Root (signedRootCoordinate (false, G2PositiveRoot.alpha))) = ζ⁻¹ := by
  rw [s1Root_alpha1_readback]
  apply phaseTable_negative
  exact (isNegative_signedRootCoordinate_iff (true, G2PositiveRoot.alpha)).2 rfl

theorem phaseTable_s2_alpha2_transition (ζ : ℂ) :
    phaseTable ζ (s2Root (signedRootCoordinate (false, G2PositiveRoot.beta))) = ζ⁻¹ := by
  rw [s2Root_alpha2_readback]
  apply phaseTable_negative
  exact (isNegative_signedRootCoordinate_iff (true, G2PositiveRoot.beta)).2 rfl

end InfoGeometry.Exceptional.G2DiagonalPhase
