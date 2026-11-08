/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Principal-ideal pairings and opposite graph charts

Source: turns 224 and 227 of the saved conversation 1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f.
Contract: arbitrary associative ring, idempotent P, unrestricted operator inputs.
The star statements additionally require a star-ring and star P = P.

Dependency order: ideal decomposition → ordered chart products → triple products;
star reversal → corner-valued pairing → grading-twisted pairing.
These are operator-valued identities, not scalar Born probabilities, positivity,
Hilbert-space norms, or a construction of a Krein space.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

/-- Decomposition of a principal left ideal into its two Peirce components. -/
theorem left_ideal_peirce_split (X : B) :
    X * P = peirce11 P X + coneMinus P X := by
  simp only [peirce11, coneMinus, sub_mul, one_mul]
  abel

/-- Decomposition of a principal right ideal into its two Peirce components. -/
theorem right_ideal_peirce_split (Y : B) :
    P * Y = peirce11 P Y + conePlus P Y := by
  simp only [peirce11, conePlus, mul_sub, mul_one]
  abel

/-- Pairing takes values in the corner ring, not in the scalar field. -/
theorem principal_ideal_pairing (X Y : B) :
    (P * Y) * (X * P) = peirce11 P (Y * X) := by
  simp only [peirce11, mul_assoc]

include hP

theorem chart_pairing_upper (A C : B) :
    (P - conePlus P A) * (P + coneMinus P C) =
      P - conePlus P A * coneMinus P C := by
  peirce_nf hP

theorem chart_pairing_lower (A C : B) :
    (P + coneMinus P C) * (P - conePlus P A) =
      P - genJ P A C - coneMinus P C * conePlus P A := by
  peirce_nf hP

theorem chart_pairing_even_commutator (A C : B) :
    evenGrade P (comm (P - conePlus P A) (P + coneMinus P C)) =
      -genSig P A C := by
  peirce_nf hP

/-- Ordered triple-product identity; no positivity interpretation is asserted. -/
theorem chart_pairing_upper_triple (A C : B) :
    (P - conePlus P A) * (P + coneMinus P C) * (P - conePlus P A) =
      (1 - genV P A C) * (P - conePlus P A) := by
  peirce_nf hP

theorem chart_pairing_lower_triple (A C : B) :
    (P + coneMinus P C) * (P - conePlus P A) * (P + coneMinus P C) =
      (P + coneMinus P C) * (1 - genV P A C) := by
  peirce_nf hP

/-- Multiplication by the grading separates the two intermediate corners. -/
theorem ideal_pairing_split (X Y : B) :
    P * Y * invS P * X * P =
      peirce11 P Y * peirce11 P X - conePlus P Y * coneMinus P X := by
  simp only [conePlus, coneMinus]
  peirce_nf hP

/-- The difference of the two charts squares to the corner anticommutator. -/
theorem chart_pairing_difference_square (A C : B) :
    ((P - conePlus P A) - (P + coneMinus P C)) *
      ((P - conePlus P A) - (P + coneMinus P C)) = genV P A C := by
  peirce_nf hP

/-- Correction to turn 227: the submitted formula omitted the term `-J`. -/
theorem chart_pairing_sum_square (A C : B) :
    ((P - conePlus P A) + (P + coneMinus P C) - P) *
      ((P - conePlus P A) + (P + coneMinus P C) - P) =
      P - genJ P A C - genV P A C := by
  peirce_nf hP

/-- Exact criterion for the shorter, generally false, formula in turn 227. -/
theorem chart_pairing_sum_square_short_iff (A C : B) :
    ((P - conePlus P A) + (P + coneMinus P C) - P) *
      ((P - conePlus P A) + (P + coneMinus P C) - P) = P - genV P A C ↔
      genJ P A C = 0 := by
  rw [chart_pairing_sum_square hP, sub_left_inj, sub_eq_self]

theorem chart_pairing_upper_defect (A C : B) :
    let T := (P - conePlus P A) * (P + coneMinus P C) * (P - conePlus P A)
    T * T - T =
      (genV P A C * genV P A C - genV P A C) * (P - conePlus P A) := by
  dsimp only
  rw [chart_pairing_upper_triple hP]
  peirce_nf hP

theorem chart_pairing_lower_defect (A C : B) :
    let T := (P + coneMinus P C) * (P - conePlus P A) * (P + coneMinus P C)
    T * T - T =
      (P + coneMinus P C) * (genV P A C * genV P A C - genV P A C) := by
  dsimp only
  rw [chart_pairing_lower_triple hP]
  peirce_nf hP

variable [StarRing B] (hPs : star P = P)
include hPs

omit hP in
/-- Adjoint reversal exchanges the two principal ideals. -/
theorem star_left_ideal (X : B) : star (X * P) = P * star X := by
  rw [star_mul, hPs]

/-- The untwisted pairing contains the sum of the two intermediate corners. -/
theorem star_ideal_pairing_split (X Y : B) :
    star (Y * P) * (X * P) =
      peirce11 P (star Y) * peirce11 P X +
        conePlus P (star Y) * coneMinus P X := by
  rw [star_mul, hPs]
  simp only [conePlus, coneMinus]
  peirce_nf hP

/-- Algebraic indefinite pairing with an explicit self-adjoint idempotent. -/
theorem twisted_ideal_pairing (X Y : B) :
    (invS P * star (Y * P) * invS P) * (X * P) =
      peirce11 P (star Y) * peirce11 P X -
        conePlus P (star Y) * coneMinus P X := by
  rw [star_mul, hPs]
  simp only [conePlus, coneMinus]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
