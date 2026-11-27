/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Krein.DoubledSpaceMatrixNoncommutativeWitness

/-!
# Lie-product transport for the native doubled-space matrix action

The native real matrix representation transports the matrix commutator to the
commutator of the represented continuous linear operators.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The native doubled-space representation preserves matrix commutators. -/
theorem ρclock_commutator
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    ρclock (E := E) (A * B - B * A) =
      (ρclock (E := E) A).comp (ρclock (E := E) B) -
        (ρclock (E := E) B).comp (ρclock (E := E) A) := by
  rw [(ρclock (E := E)).map_sub, ρclock_mul, ρclock_mul]

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_commutator
