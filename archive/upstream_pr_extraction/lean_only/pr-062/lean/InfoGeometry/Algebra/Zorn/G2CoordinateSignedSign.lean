/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge

namespace InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots

theorem isNegative_signedRootCoordinate_iff
    (r : Bool × G2PositiveRoot) :
    isNegative (signedRootCoordinate r) ↔ r.1 = true := by
  classical
  rcases r with ⟨b, α⟩
  cases b <;> cases α <;>
    simp [isNegative, signedRootCoordinate, positiveRootInFullCarrier,
      phiMinus, G2Roots.phiPlus, rootCoordinates]

theorem isPositive_signedRootCoordinate_iff
    (r : Bool × G2PositiveRoot) :
    isPositive (signedRootCoordinate r) ↔ r.1 = false := by
  classical
  rcases r with ⟨b, α⟩
  cases b <;> cases α <;>
    simp [isPositive, signedRootCoordinate, positiveRootInFullCarrier,
      phiMinus, G2Roots.phiPlus, rootCoordinates]

end InfoGeometry.Algebra.Zorn.G2CoordinateSignedSign
