/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing

/-!
# q-commutation and the Jordan--Lie readout

For elements of an arbitrary (possibly noncommutative) ring, the relation
`X * Y = q * (Y * X)` has two exact readouts.  This file keeps the coefficient
on the left, so no centrality or division hypothesis is hidden in the basic
results.
-/

namespace InfoGeometry.Algebra.QHeisenberg

variable {A : Type*} [Ring A]

/-- The left-coefficient q-commutation relation. -/
def QCommutes (q X Y : A) : Prop :=
  X * Y = q * (Y * X)

/-- The ordinary commutator in an associative ring. -/
def comm (X Y : A) : A := X * Y - Y * X

/-- The ordinary anticommutator in an associative ring. -/
def anti (X Y : A) : A := X * Y + Y * X

/-- The commutator readout of a q-commuting pair. -/
theorem comm_eq_of_QCommutes (q X Y : A)
    (h : QCommutes q X Y) :
    comm X Y = (q - 1) * (Y * X) := by
  unfold comm QCommutes at *
  rw [h]
  noncomm_ring

/-- The anticommutator readout of a q-commuting pair. -/
theorem anti_eq_of_QCommutes (q X Y : A)
    (h : QCommutes q X Y) :
    anti X Y = (q + 1) * (Y * X) := by
  unfold anti QCommutes at *
  rw [h]
  noncomm_ring

/-- The division-free Jordan--Lie identity forced by q-commutation. -/
theorem comm_anti_relation (q X Y : A)
    (h : QCommutes q X Y) :
    (q + 1) * comm X Y = (q - 1) * anti X Y := by
  rw [comm_eq_of_QCommutes q X Y h, anti_eq_of_QCommutes q X Y h]
  noncomm_ring

/-- At `q = 1`, q-commutation forces the commutator to vanish. -/
theorem comm_eq_zero_of_QCommutes_one (X Y : A)
    (h : QCommutes 1 X Y) :
    comm X Y = 0 := by
  simpa [comm_eq_of_QCommutes (1 : A) X Y h]

/-- At `q = -1`, q-commutation forces the anticommutator to vanish. -/
theorem anti_eq_zero_of_QCommutes_neg_one (X Y : A)
    (h : QCommutes (-1 : A) X Y) :
    anti X Y = 0 := by
  simpa [anti_eq_of_QCommutes (-1 : A) X Y h]

end InfoGeometry.Algebra.QHeisenberg
