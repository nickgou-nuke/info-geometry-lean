/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2CircularRootComplementLabel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

namespace InfoGeometry.Exceptional.G2ComplementMixingReadback

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots
open InfoGeometry.Exceptional.G2CircularRootLabelTransport
open InfoGeometry.Exceptional.G2CircularRootComplementLabel

theorem s1_complement_three_alpha_beta_to_circular_beta :
    s1Root (complementRootLabel 2) = circularRootTransport.label 7 := by
  apply Subtype.ext
  simp [s1Root, complementRootLabel, signedRootCoordinate,
    circularRootTransport, circularRootLabel, s1, rootCoordinates]

theorem s2_complement_alpha_add_beta_to_circular_alpha :
    s2Root (complementRootLabel 0) = circularRootTransport.label 6 := by
  apply Subtype.ext
  simp [s2Root, complementRootLabel, signedRootCoordinate,
    circularRootTransport, circularRootLabel, s2, rootCoordinates]

end InfoGeometry.Exceptional.G2ComplementMixingReadback
