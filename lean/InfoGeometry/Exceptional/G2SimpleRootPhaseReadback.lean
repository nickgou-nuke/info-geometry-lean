/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2DiagonalPhaseTable
import InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

namespace InfoGeometry.Exceptional.G2DiagonalPhase

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots

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

end InfoGeometry.Exceptional.G2DiagonalPhase
