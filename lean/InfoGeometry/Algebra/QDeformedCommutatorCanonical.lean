/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Algebra.QDeformedCommutatorCanonical

variable {A : Type*} [Ring A]

/-- The homogeneous q-commutation relation with the deformation coefficient on the left. -/
def QCommutes (q X Y : A) : Prop := X * Y = q * (Y * X)

/-- The ordinary commutator. -/
def comm (X Y : A) : A := X * Y - Y * X

/-- The ordinary anticommutator. -/
def anti (X Y : A) : A := X * Y + Y * X

/-- A homogeneous q-commutation relation determines the commutator. -/
theorem comm_eq_of_qCommutes (q X Y : A) (h : QCommutes q X Y) :
    comm X Y = (q - 1) * (Y * X) := by
  unfold comm QCommutes at *
  rw [h]
  noncomm_ring

/-- A homogeneous q-commutation relation determines the anticommutator. -/
theorem anti_eq_of_qCommutes (q X Y : A) (h : QCommutes q X Y) :
    anti X Y = (q + 1) * (Y * X) := by
  unfold anti QCommutes at *
  rw [h]
  noncomm_ring

/-- The division-free commutator/anticommutator identity. -/
theorem comm_anti_relation_of_qCommutes (q X Y : A) (h : QCommutes q X Y) :
    (q + 1) * comm X Y = (q - 1) * anti X Y := by
  rw [comm_eq_of_qCommutes q X Y h, anti_eq_of_qCommutes q X Y h]
  noncomm_ring

/-- The commutator vanishes in the commuting endpoint `q = 1`. -/
theorem comm_eq_zero_of_qCommutes_one (X Y : A) (h : QCommutes 1 X Y) :
    comm X Y = 0 := by
  rw [comm_eq_of_qCommutes 1 X Y h]
  noncomm_ring

/-- The anticommutator vanishes in the anticommuting endpoint `q = -1`. -/
theorem anti_eq_zero_of_qCommutes_neg_one (X Y : A) (h : QCommutes (-1) X Y) :
    anti X Y = 0 := by
  rw [anti_eq_of_qCommutes (-1) X Y h]
  noncomm_ring

end InfoGeometry.Algebra.QDeformedCommutatorCanonical
