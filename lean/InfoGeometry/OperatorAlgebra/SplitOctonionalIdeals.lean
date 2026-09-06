import InfoGeometry.OperatorAlgebra.ColeFuryIdeals

/-!
# Split-octonional ideal projector surface

This module is the Lean twin of `tools/sympy/split_octonional_ideals.py`.
It exposes the finite ideal-absorption laws inherited from the verified
Cole-Fury `32 × 32` quadrant decomposition.

#### BUCKET 1: CLOSED FINITE THEOREMS
The declarations below prove:

* any idempotent matrix projector `P` absorbs on the right: `(R * P) * P = R * P`;
* the dual left absorption law: `P * (P * R) = P * R`;
* the concrete `upperLeft` and `lowerRight` quadrant projectors satisfy both laws;
* the horizon incidence laws between diagonal ideals and off-diagonal horizon
  maps are exact finite matrix equalities.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not formalize full split-octonion multiplication, nonassociative
Moufang laws, `G₂(2)` automorphisms, or a physical particle classification.  It
locks the finite projector/ideal absorption surface that can later receive a
true split-octonion multiplication layer.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions

open Matrix
open InfoGeometry.OperatorAlgebra.ColeFury

abbrev Spin32Matrix := Matrix (Fin 32) (Fin 32) ℤ

/-- Predicate for a finite matrix projector used as an ideal carrier. -/
def IsIdealProjector (P : Spin32Matrix) : Prop := P * P = P

/-- Any idempotent projector absorbs right multiplication by itself. -/
theorem right_absorption_of_idempotent (P R : Spin32Matrix) (hP : IsIdealProjector P) :
    (R * P) * P = R * P := by
  rw [Matrix.mul_assoc, hP]

/-- Any idempotent projector absorbs left multiplication by itself. -/
theorem left_absorption_of_idempotent (P R : Spin32Matrix) (hP : IsIdealProjector P) :
    P * (P * R) = P * R := by
  rw [← Matrix.mul_assoc, hP]

/-- The upper-left quadrant is a finite ideal projector. -/
theorem upperLeft_isIdealProjector : IsIdealProjector upperLeft :=
  upperLeft_idempotent

/-- The lower-right quadrant is a finite ideal projector. -/
theorem lowerRight_isIdealProjector : IsIdealProjector lowerRight :=
  lowerRight_idempotent

/-- Upper-left right ideal absorption for any finite ambient matrix. -/
theorem upperLeft_right_absorption (R : Spin32Matrix) :
    (R * upperLeft) * upperLeft = R * upperLeft :=
  right_absorption_of_idempotent upperLeft R upperLeft_isIdealProjector

/-- Upper-left left ideal absorption for any finite ambient matrix. -/
theorem upperLeft_left_absorption (R : Spin32Matrix) :
    upperLeft * (upperLeft * R) = upperLeft * R :=
  left_absorption_of_idempotent upperLeft R upperLeft_isIdealProjector

/-- Lower-right right ideal absorption for any finite ambient matrix. -/
theorem lowerRight_right_absorption (R : Spin32Matrix) :
    (R * lowerRight) * lowerRight = R * lowerRight :=
  right_absorption_of_idempotent lowerRight R lowerRight_isIdealProjector

/-- Lower-right left ideal absorption for any finite ambient matrix. -/
theorem lowerRight_left_absorption (R : Spin32Matrix) :
    lowerRight * (lowerRight * R) = lowerRight * R :=
  left_absorption_of_idempotent lowerRight R lowerRight_isIdealProjector

/-- Upper-left projection kills an incoming lower-left horizon from the left. -/
theorem upperLeft_horizonDown_zero : upperLeft * horizonDown = 0 := by
  unfold upperLeft horizonDown
  decide

/-- Lower-right projection kills an incoming upper-right horizon from the left. -/
theorem lowerRight_horizonUp_zero : lowerRight * horizonUp = 0 := by
  unfold lowerRight horizonUp
  decide

/-- Upper-left projection preserves the outgoing upper-right horizon. -/
theorem upperLeft_horizonUp : upperLeft * horizonUp = horizonUp := by
  unfold upperLeft horizonUp
  decide

/-- Lower-right projection preserves the incoming lower-left horizon. -/
theorem lowerRight_horizonDown : lowerRight * horizonDown = horizonDown := by
  unfold lowerRight horizonDown
  decide

/-- Upper-right horizon lands in the lower-right quadrant on the right. -/
theorem horizonUp_lowerRight : horizonUp * lowerRight = horizonUp := by
  unfold horizonUp lowerRight
  decide

/-- Lower-left horizon lands in the upper-left quadrant on the right. -/
theorem horizonDown_upperLeft : horizonDown * upperLeft = horizonDown := by
  unfold horizonDown upperLeft
  decide

/-- Upper-right horizon is killed by the upper-left quadrant on the right. -/
theorem horizonUp_upperLeft_zero : horizonUp * upperLeft = 0 := by
  unfold horizonUp upperLeft
  decide

/-- Lower-left horizon is killed by the lower-right quadrant on the right. -/
theorem horizonDown_lowerRight_zero : horizonDown * lowerRight = 0 := by
  unfold horizonDown lowerRight
  decide
