/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-!
# Faithfulness of the native doubled-space matrix action

The standard real `2 × 2` matrix action on the native doubled carrier is
faithful whenever the coefficient space is nontrivial.  The proof recovers
the two columns by evaluating on the two coordinate vectors built from one
nonzero coefficient-space element.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- The native matrix representation on `DoubledSpace E` is injective when
`E` contains a nonzero vector. -/
theorem ρclock_injective [Nontrivial E] :
    Function.Injective (ρclock (E := E)) := by
  intro A B h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hfirst := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
      WithLp.fst (T (to_doubled x 0 : DoubledSpace E))) h
  have hsecond := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
      WithLp.snd (T (to_doubled x 0 : DoubledSpace E))) h
  have hthird := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
      WithLp.fst (T (to_doubled 0 x : DoubledSpace E))) h
  have hfourth := congrArg
    (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
      WithLp.snd (T (to_doubled 0 x : DoubledSpace E))) h
  have h00 : A 0 0 = B 0 0 := by
    apply smul_left_injective ℝ hx
    simpa [ρclock, matrixAction] using hfirst
  have h10 : A 1 0 = B 1 0 := by
    apply smul_left_injective ℝ hx
    simpa [ρclock, matrixAction] using hsecond
  have h01 : A 0 1 = B 0 1 := by
    apply smul_left_injective ℝ hx
    simpa [ρclock, matrixAction] using hthird
  have h11 : A 1 1 = B 1 1 := by
    apply smul_left_injective ℝ hx
    simpa [ρclock, matrixAction] using hfourth
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_injective
