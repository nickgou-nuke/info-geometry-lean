/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset

/-!
# Fifth iterated charge closure for the five Kantor–Peirce sectors

The existing owner supplies the five grade eigenvalue identities and the
first four iterated charge expansions. This module adds the fifth iterate
and proves its characteristic polynomial identity directly in the same
noncommutative ring model. The integral projector formulas remain scaled
(`12` or `24` times a sector); no inverse of those integers is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Fifth iterate of the superoperator charge derivation on the total
Kantor–Peirce operator. -/
def kantorDelta5 (P A C X : B) : B :=
  superChargeP (kantorDelta4 P A C) P X

/-- The fifth iterate acts on the five charge channels with their fifth-power
weights: `(-2)^5`, `(-1)^5`, `0^5`, `1^5`, and `2^5`. -/
theorem kantorDelta5_expansion
    {P : B} (hP : P * P = P) (A C : B) (X : B) :
    kantorDelta5 P A C X =
      -((32 : ℤ) • kantorGm2 P C X) - kantorGm1 P C X +
        kantorGp1 P A X + (32 : ℤ) • kantorGp2 P A X := by
  unfold kantorDelta5 kantorDelta4 kantorDelta3 kantorDelta2 kantorDelta1
    superChargeP kantorTotal
  peirce_abel_golay hP

/-- The fifth iterate obeys the minimal odd polynomial for charge values
`-2, -1, 0, 1, 2`: `Δ⁵ - 5 Δ³ + 4 Δ = 0`. -/
theorem kantorDelta5_master_closure
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorDelta5 P A C X - (5 : ℤ) • kantorDelta3 P A C X +
      (4 : ℤ) • kantorDelta1 P A C X = 0 := by
  unfold kantorDelta5 kantorDelta4 kantorDelta3 kantorDelta2 kantorDelta1
    superChargeP kantorTotal
  peirce_abel_golay hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
