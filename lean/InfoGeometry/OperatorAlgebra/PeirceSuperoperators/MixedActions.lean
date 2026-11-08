/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanMultiplicationClosure
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Lie and Jordan compositions on the full associative algebra

The native inner Lie action and the existing unnormalized Jordan action have
different squares. Their mixed difference retains a two-sided transport term;
it is not the operator commutator already owned by `JordanAssociator`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open InfoGeometry.Core.JordanMultiplicationClosure

attribute [local instance] LieRing.ofAssociativeRing

section Algebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

local notation "D" => LieAlgebra.ad R A
local notation "J" => jordanLeft (R := R)
local notation "L" => LinearMap.mulLeft R
local notation "M" => LinearMap.mulRight R

/-- The symmetric mixed composition is an inner Lie action. -/
theorem lie_jordan_sum (u v : A) :
    D u * J v + D v * J u = D (u * v + v * u) := by
  ext x
  change (u * (v * x + x * v) - (v * x + x * v) * u) +
    (v * (u * x + x * u) - (u * x + x * u) * v) =
      (u * v + v * u) * x - x * (u * v + v * u)
  noncomm_ring

/-- The opposite mixed order has the same symmetric sum. -/
theorem jordan_lie_sum (u v : A) :
    J u * D v + J v * D u = D (u * v + v * u) := by
  ext x
  change (u * (v * x - x * v) + (v * x - x * v) * u) +
    (v * (u * x - x * u) + (u * x - x * u) * v) =
      (u * v + v * u) * x - x * (u * v + v * u)
  noncomm_ring

/-- The exact correction to the source's unrestricted mixed-difference claim. -/
theorem lie_jordan_difference (u v : A) :
    D u * J v - D v * J u =
      J ⁅u, v⁆ + 2 • (L u * M v - L v * M u) := by
  ext x
  change (u * (v * x + x * v) - (v * x + x * v) * u) -
    (v * (u * x + x * u) - (u * x + x * u) * v) =
      (u * v - v * u) * x + x * (u * v - v * u) +
        2 • (u * (x * v) - v * (x * u))
  simp only [two_nsmul]
  noncomm_ring

/-- In the opposite mixed order the sandwich correction has the opposite sign. -/
theorem jordan_lie_difference (u v : A) :
    J u * D v - J v * D u =
      J ⁅u, v⁆ - 2 • (L u * M v - L v * M u) := by
  ext x
  change (u * (v * x - x * v) + (v * x - x * v) * u) -
    (v * (u * x - x * u) + (u * x - x * u) * v) =
      (u * v - v * u) * x + x * (u * v - v * u) -
        2 • (u * (x * v) - v * (x * u))
  simp only [two_nsmul]
  noncomm_ring

theorem lie_lie_sum (u v : A) :
    D u * D v + D v * D u =
      J (u * v + v * u) - 2 • (L u * M v + L v * M u) := by
  ext x
  change (u * (v * x - x * v) - (v * x - x * v) * u) +
    (v * (u * x - x * u) - (u * x - x * u) * v) =
      (u * v + v * u) * x + x * (u * v + v * u) -
        2 • (u * (x * v) + v * (x * u))
  simp only [two_nsmul]
  noncomm_ring

theorem jordan_jordan_sum (u v : A) :
    J u * J v + J v * J u =
      J (u * v + v * u) + 2 • (L u * M v + L v * M u) := by
  ext x
  change (u * (v * x + x * v) + (v * x + x * v) * u) +
    (v * (u * x + x * u) + (u * x + x * u) * v) =
      (u * v + v * u) * x + x * (u * v + v * u) +
        2 • (u * (x * v) + v * (x * u))
  simp only [two_nsmul]
  noncomm_ring

/-- Division-free recovery of the two-sided symmetric transport. -/
theorem pure_composition_difference (u v : A) :
    (J u * J v + J v * J u) - (D u * D v + D v * D u) =
      4 • (L u * M v + L v * M u) := by
  rw [jordan_jordan_sum, lie_lie_sum]
  abel

theorem pure_composition_sum (u v : A) :
    (J u * J v + J v * J u) + (D u * D v + D v * D u) =
      2 • J (u * v + v * u) := by
  rw [jordan_jordan_sum, lie_lie_sum]
  abel

theorem lie_jordan_same (u : A) : D u * J u = D (u * u) := by
  ext x
  change u * (u * x + x * u) - (u * x + x * u) * u =
    (u * u) * x - x * (u * u)
  noncomm_ring

theorem jordan_lie_same (u : A) : J u * D u = D (u * u) := by
  ext x
  change u * (u * x - x * u) + (u * x - x * u) * u =
    (u * u) * x - x * (u * u)
  noncomm_ring

/-- An ordinary inner Lie action has a sandwich term in its square. -/
theorem lie_action_square (u : A) :
    D u * D u = J (u * u) - 2 • (L u * M u) := by
  ext x
  change u * (u * x - x * u) - (u * x - x * u) * u =
    (u * u) * x + x * (u * u) - 2 • (u * (x * u))
  simp only [two_nsmul]
  noncomm_ring

theorem jordan_action_square (u : A) :
    J u * J u = J (u * u) + 2 • (L u * M u) := by
  ext x
  change u * (u * x + x * u) + (u * x + x * u) * u =
    (u * u) * x + x * (u * u) + 2 • (u * (x * u))
  simp only [two_nsmul]
  noncomm_ring

theorem lie_jordan_eq_zero_of_square_zero (u : A) (hu : u * u = 0) :
    D u * J u = 0 := by
  rw [lie_jordan_same, hu, map_zero]

theorem jordan_lie_eq_zero_of_square_zero (u : A) (hu : u * u = 0) :
    J u * D u = 0 := by
  rw [jordan_lie_same, hu, map_zero]

end Algebra

section Trace

variable {n R : Type*} [Fintype n] [CommRing R]

/-- Cyclic trace gives this transport identity for every input, without parity. -/
theorem trace_symmetric_sandwich (u v x : Matrix n n R) :
    (u * x * v + v * x * u).trace = ((u * v + v * u) * x).trace := by
  rw [Matrix.trace_add, add_mul, Matrix.trace_add,
    Matrix.trace_mul_cycle u x v, Matrix.trace_mul_cycle v x u, add_comm]

end Trace

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
