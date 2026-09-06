/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.Zorn.G2SignedRootReflections

/-!
# Coordinate/signed-root compatibility

The signed finite root carrier and the full integer-coordinate carrier are two
presentations of the same simple-reflection action.  This owner records that
compatibility without introducing a second Weyl group or a new root table.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2PositiveRootCoordinateBridge
open InfoGeometry.Algebra.Zorn.G2Roots
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections

theorem signedRootCoordinate_simpleReflectionOne (r : SignedPositiveRoot) :
    signedRootCoordinate (simpleReflectionOne r) =
      s1Root (signedRootCoordinate r) := by
  cases r with
  | mk sign α => cases sign <;> cases α <;> rfl

theorem signedRootCoordinate_simpleReflectionTwo (r : SignedPositiveRoot) :
    signedRootCoordinate (simpleReflectionTwo r) =
      s2Root (signedRootCoordinate r) := by
  cases r with
  | mk sign α => cases sign <;> cases α <;> rfl

theorem signedRootCoordinate_simpleWordAction (word : List Bool)
    (r : SignedPositiveRoot) :
    signedRootCoordinate (simpleWordAction word r) =
      (word.foldl (fun e bit =>
        if bit then s1Root e else s2Root e) (signedRootCoordinate r)) := by
  induction word generalizing r with
  | nil => rfl
  | cons bit word ih =>
      simp only [simpleWordAction, List.foldl_cons]
      by_cases hbit : bit
      · simp [hbit, signedRootCoordinate_simpleReflectionOne, ih]
      · simp [hbit, signedRootCoordinate_simpleReflectionTwo, ih]

end InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge
