/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity

/-!
# Peirce components of the idempotency defect

Contract: arbitrary associative ring, idempotent P, and the existing Peirce
projections. Dependency order: corner relations → graded defect split → odd
perturbation criterion → ordered parity product and its sign boundary.
Parity equivariance uses the existing ring equivalence. No division by two,
Galois-extension classification, or cohomology vanishing is asserted.
In characteristic two parity eigenconditions do not recover Peirce grades.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

variable {P : B} (hP : P * P = P)
include hP

/-- The exact condition is square-zero, not vanishing of the perturbation. -/
theorem add_oddGrade_idempotent_iff (X : B) :
    (P + oddGrade P X) * (P + oddGrade P X) = P + oddGrade P X ↔
      oddGrade P X * oddGrade P X = 0 := by
  rw [← idempotencyDefect_eq_zero_iff, odd_perturbation_defect hP]

/-- Ordered parity products have a negative commutator term. -/
theorem add_oddGrade_mul_parityConj (X : B) :
    (P + oddGrade P X) * parityConj P (P + oddGrade P X) =
      P - oddGrade P X * oddGrade P X - comm P (oddGrade P X) := by
  unfold parityConj
  peirce_nf hP

theorem add_oddGrade_mul_parityConj_plus_sign_iff (X : B) :
    (P + oddGrade P X) * parityConj P (P + oddGrade P X) =
        P - oddGrade P X * oddGrade P X + comm P (oddGrade P X) ↔
      (2 : ℤ) • comm P (oddGrade P X) = 0 := by
  rw [add_oddGrade_mul_parityConj hP, two_zsmul]
  constructor
  · intro h
    have hn : -comm P (oddGrade P X) = comm P (oddGrade P X) :=
      add_left_cancel (by simpa only [sub_eq_add_neg] using h)
    calc
      comm P (oddGrade P X) + comm P (oddGrade P X) =
          -comm P (oddGrade P X) + comm P (oddGrade P X) :=
        congrArg (fun t => t + comm P (oddGrade P X)) hn.symm
      _ = 0 := neg_add_cancel _
  · intro h
    have hn : -comm P (oddGrade P X) = comm P (oddGrade P X) := by
      calc
        -comm P (oddGrade P X) = -comm P (oddGrade P X) +
            (comm P (oddGrade P X) + comm P (oddGrade P X)) := by rw [h, add_zero]
        _ = comm P (oddGrade P X) := by abel
    rw [sub_eq_add_neg, hn]

end InfoGeometry.OperatorAlgebra.PeirceSpine
