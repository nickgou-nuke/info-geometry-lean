/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Commutator covariance under ring homomorphisms

This module proves the algebraic covariance statement needed when transporting
commutation relations. It does not assert a quantitative Lieb–Robinson bound:
that requires a norm, a metric on supports, and a proved estimate for the
chosen dynamics.
-/

namespace InfoGeometry.Algebra.LiebRobinsonBounds

/-- The associative-ring commutator. -/
def commutator {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X

/-- A ring homomorphism carries the source commutator to the target commutator. -/
theorem ringHom_map_commutator {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (X Y : R) :
    f (commutator X Y) = commutator (f X) (f Y) := by
  simp [commutator, map_sub, map_mul]

/-- Ring homomorphisms preserve a zero commutator. -/
theorem ringHom_preserves_commutation {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) {X Y : R}
    (hXY : commutator X Y = 0) :
    commutator (f X) (f Y) = 0 := by
  rw [← ringHom_map_commutator]
  rw [hXY]
  exact map_zero f

end InfoGeometry.Algebra.LiebRobinsonBounds
