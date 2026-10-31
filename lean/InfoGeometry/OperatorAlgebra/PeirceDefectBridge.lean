/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity

/-!
# Peirce boundary contribution to the idempotency defect

The statements below use the existing Peirce spine owners.  They express a
ring identity in an arbitrary associative, potentially noncommutative ring;
they do not identify this boundary term with analytic flux or tensor
separability.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDefectBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The square of the odd Peirce component is the two-sided boundary
contraction (the `genV` operator with both inputs equal to `X`). -/
theorem oddGrade_square_eq_genV (P X : B) (hP : P * P = P) :
    oddGrade P X * oddGrade P X = genV P X X := by
  simp only [oddGrade, genV, anticomm, conePlus, coneMinus]
  peirce_nf hP

/-- Pinching the idempotency defect and taking the defect after pinching
differ by exactly the boundary quadratic term. The sign follows the convention
`idempotencyDefect X = X * X - X`. -/
theorem even_idempotencyDefect_sub (P X : B) (hP : P * P = P) :
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) =
      genV P X X := by
  rw [even_idempotencyDefect hP X, oddGrade_square_eq_genV P X hP]
  noncomm_ring

/-- If `X` is idempotent, its Peirce pinching has defect equal to the negative
boundary quadratic term. -/
theorem idempotencyDefect_evenGrade_of_idempotent
    (P X : B) (hP : P * P = P) (hX : X * X = X) :
    idempotencyDefect (evenGrade P X) = -genV P X X := by
  have h := even_idempotencyDefect_sub P X hP
  have hXdef : idempotencyDefect X = 0 := by
    simp [idempotencyDefect, hX]
  rw [hXdef] at h
  simp only [evenGrade, zero_mul, mul_zero, add_zero, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

end InfoGeometry.OperatorAlgebra.PeirceDefectBridge
