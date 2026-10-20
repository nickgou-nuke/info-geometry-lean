/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.NoncommRing

/-!
# Exact commutator--anticommutator decomposition of a q-exchange relation

This owner records the algebraic content of `X * Y = q * (Y * X)` in an
arbitrary (possibly noncommutative) ring.  The coefficient `q` is an element
of the same ring; no centrality or division assumption is made.
-/

namespace InfoGeometry.Algebra.QHeisenberg

variable {A : Type*} [Ring A]

/-- The left-coefficient q-exchange relation. -/
def QCommutes (q X Y : A) : Prop :=
  X * Y = q * (Y * X)

/-- The ordinary commutator. -/
def commutator (X Y : A) : A := X * Y - Y * X

/-- The ordinary anticommutator. -/
def anticommutator (X Y : A) : A := X * Y + Y * X

theorem commutator_eq
    (q X Y : A) (h : QCommutes q X Y) :
    commutator X Y = (q - 1) * (Y * X) := by
  unfold commutator QCommutes at *
  rw [h]
  noncomm_ring

theorem anticommutator_eq
    (q X Y : A) (h : QCommutes q X Y) :
    anticommutator X Y = (q + 1) * (Y * X) := by
  unfold anticommutator QCommutes at *
  rw [h]
  noncomm_ring

/-- The division-free commutator--anticommutator identity. -/
theorem commutator_anticommutator_relation
    (q X Y : A) (h : QCommutes q X Y) :
    (q + 1) * commutator X Y = (q - 1) * anticommutator X Y := by
  rw [commutator_eq q X Y h, anticommutator_eq q X Y h]
  noncomm_ring

theorem commutator_eq_zero_of_q_eq_one
    (X Y : A) (h : QCommutes 1 X Y) :
    commutator X Y = 0 := by
  rw [commutator_eq 1 X Y h]
  noncomm_ring

theorem anticommutator_eq_zero_of_q_eq_neg_one
    (X Y : A) (h : QCommutes (-1) X Y) :
    anticommutator X Y = 0 := by
  rw [anticommutator_eq (-1) X Y h]
  noncomm_ring

end InfoGeometry.Algebra.QHeisenberg
