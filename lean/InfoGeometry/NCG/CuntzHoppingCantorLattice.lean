/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import Mathlib.Tactic

/-!
# Injectivity of the Existing Cuntz Shift

This owner reuses `CuntzSystem` and `CuntzSystem.canonicalShift` from
`CuntzColimitKMSTiltGNS`. It makes no second Cuntz-family carrier and claims no
Cantor-boundary action. The result below is a new consequence of the existing
generator-level left-inverse theorem.
-/

namespace InfoGeometry.NCG.CuntzHoppingCantorLattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [StarRing A]

/-- The canonical Cuntz shift is injective: a specified generator's
left-inverse identity recovers its input. -/
theorem canonicalShift_injective (C : CuntzSystem ι A) (j : ι) :
    Function.Injective C.canonicalShift := by
  intro X Y hXY
  have h := congrArg (fun Z : A => star (C.S j) * Z * C.S j) hXY
  rw [C.shift_left_inverse j X, C.shift_left_inverse j Y] at h
  exact h

end InfoGeometry.NCG.CuntzHoppingCantorLattice
