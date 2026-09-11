/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Word-level transport of the signed Weyl action

Finite words in the canonical signed-root reflection owner are transported to
permutations of the full coordinate root carrier.  No new Weyl multiplication
law is introduced here.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge

open InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections

def coordinateWordAction : List Bool → Equiv.Perm G2CoordinateRoot
  | [] => 1
  | bit :: word =>
      (if bit then s1Root else s2Root).trans (coordinateWordAction word)

theorem coordinateWordAction_append (u v : List Bool) :
    coordinateWordAction (u ++ v) =
      coordinateWordAction v * coordinateWordAction u := by
  induction u with
  | nil => simp [coordinateWordAction]
  | cons bit u ih =>
      simp only [List.cons_append, coordinateWordAction]
      rw [ih]
      cases bit <;>
        apply Equiv.ext <;> intro x <;>
        simp [Equiv.Perm.mul_def, Equiv.trans_apply]

theorem coordinateWordAction_apply_signed
    (word : List Bool) (r : SignedPositiveRoot) :
    coordinateWordAction word (signedRootCoordinate r) =
      signedRootCoordinate (simpleWordAction word r) := by
  induction word generalizing r with
  | nil => rfl
  | cons bit word ih =>
      simp only [coordinateWordAction]
      cases bit with
      | false =>
        rw [if_neg Bool.false_ne_true]
        change (coordinateWordAction word) (s2Root (signedRootCoordinate r)) = _
        rw [show simpleWordAction (false :: word) r =
          simpleWordAction word (simpleReflectionTwo r) by rfl]
        rw [← signedRootCoordinate_simpleReflectionTwo]
        exact ih _
      | true =>
        rw [if_pos rfl]
        change (coordinateWordAction word) (s1Root (signedRootCoordinate r)) = _
        rw [show simpleWordAction (true :: word) r =
          simpleWordAction word (simpleReflectionOne r) by rfl]
        rw [← signedRootCoordinate_simpleReflectionOne]
        exact ih _

end InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
