import InfoGeometry.Meta.DvorakTactics
import InfoGeometry.Core.ExtendedField

namespace InfoGeometry.Test

open InfoGeometry.Core

/-!
# Dvořák Toolchain System Test

Testing `aeply` and `Extend F` integration.
-/

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- 
Test `aeply` with a simple implication.
The `try intro` in `aeply` handles the binder `h`, 
`apply` handles the main goal, and `aesop` is there for side-goals.
-/
theorem test_aeply_basic (h : True) : True := by
  aeply h
  trivial

/--
Test `Extend F` coercion and basic ordering.
-/
theorem test_extend_coe_le (x y : F) (h : x ≤ y) : (x : Extend F) ≤ (y : Extend F) := by
  change (((WithTop.some x : WithTop F) : WithBot (WithTop F)) ≤
    ((WithTop.some y : WithTop F) : WithBot (WithTop F)))
  exact WithBot.coe_le_coe.mpr (by simpa using h)

/--
Test `aeply` with a more complex "validity" style goal.
-/
theorem test_aeply_validity (h : True) : True := by
  aeply h
  trivial

end InfoGeometry.Test
