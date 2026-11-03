/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TelegrapherTwoStateMasterPoset

/-!
# The star-input defect in Krein transport of the quadratic Xi operator

Krein reflection transports `xiCenteredOp X` exactly. Replacing `X` with
`star X` on only the input side is a stronger, generally invalid claim. This
module gives its exact noncommutative defect and the necessary-and-sufficient
condition for that proposed equality.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section KreinXiStarDefect

variable {B : Type*} [Ring B] [StarRing B] {P X : B}

/-- The difference between the incorrectly star-shifted Xi transport and the
valid Krein transport is the Krein conjugate of the square-star defect. -/
theorem krein_xi_star_input_defect (hP : P * P = P) :
    kreinReflect P (xiCenteredOp (star X)) -
        xiCenteredOp (kreinReflect P X) =
      invS P * (star X * star X - X * X) * invS P := by
  have hS : invS P * invS P = 1 := by peirce_nf hP
  have hConjugate :
      invS P * (1 - X * X) * invS P =
        1 - invS P * (X * X) * invS P := by
    calc
      invS P * (1 - X * X) * invS P =
          invS P * invS P - invS P * (X * X) * invS P := by noncomm_ring
      _ = 1 - invS P * (X * X) * invS P := by rw [hS]
  have hSquare :
      (invS P * star X * invS P) * (invS P * star X * invS P) =
        invS P * (star X * star X) * invS P := by
    calc
      (invS P * star X * invS P) * (invS P * star X * invS P) =
          invS P * star X * (invS P * invS P) * star X * invS P := by
            noncomm_ring
      _ = invS P * (star X * star X) * invS P := by
            rw [hS]
            noncomm_ring
  unfold kreinReflect xiCenteredOp
  rw [star_sub, star_one, star_mul, star_star, hConjugate, hSquare]
  noncomm_ring

/-- The proposed star-input transport equality holds exactly when `X` and
`star X` have equal squares. No commutativity assumption is used. -/
theorem krein_xi_star_input_eq_iff_square_eq (hP : P * P = P) :
    kreinReflect P (xiCenteredOp (star X)) =
        xiCenteredOp (kreinReflect P X) ↔
      star X * star X = X * X := by
  rw [← sub_eq_zero, krein_xi_star_input_defect hP]
  constructor
  · intro h
    have hS : invS P * invS P = 1 := by peirce_nf hP
    have h := congrArg (fun Z : B => invS P * Z * invS P) h
    have h' : invS P *
        (invS P * (star X * star X - X * X) * invS P) * invS P = 0 := by
      simpa using h
    have hzero : star X * star X - X * X = 0 := by
      calc
        star X * star X - X * X =
            (invS P * invS P) * (star X * star X - X * X) *
              (invS P * invS P) := by rw [hS, one_mul, mul_one]
        _ = invS P *
            (invS P * (star X * star X - X * X) * invS P) * invS P := by
              noncomm_ring
        _ = 0 := h'
    exact sub_eq_zero.mp hzero
  · intro h
    rw [h]
    simp

end KreinXiStarDefect

end InfoGeometry.OperatorAlgebra.PeirceSpine
