/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.A2WeylFin3Action
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact order and braid behavior of the concrete type-A₂ action

The carrier is the actual permutation group `Equiv.Perm (Fin 3)`, with the
reflection and three-cycle supplied by `A2WeylFin3Action`. The theorems below
record exact orders and the non-abelian relation of these concrete generators.
They do not assert a result for arbitrary operator rings.

#### BUCKET 1: CLOSED FINITE THEOREMS
Exact orders of the reflection and cycle, their conjugation relation, and
noncommutativity in the explicit permutation action on `Fin 3`.

#### BUCKET 2: CONDITIONAL THEOREMS
None; all claims are unconditional for the concrete generators defined here.

#### BUCKET 3: UNCLAIMED GENERALIZATIONS
No generalization to arbitrary Weyl-group actions, operator rings, or
continuous Lie groups is claimed.
-/

namespace InfoGeometry.Canonical.A2WeylPermutationAction

open InfoGeometry.Canonical.A2WeylFin3Action

/-- The Weyl group of type `A₂` in its concrete action on three colours. -/
abbrev WeylA2 := Equiv.Perm (Fin 3)

/-- View an element through the ambient permutation action on `Fin 3`. -/
def asPermFin3 (p : WeylA2) : Equiv.Perm (Fin 3) := p

/-- The reflection generator acting on the three colours. -/
def rho : WeylA2 := rho3

/-- The cyclic generator acting on the three colours. -/
def shiftC : WeylA2 := shiftC3

/-- `rho` has exact order two: it is an involution and is not the identity. -/
theorem rho_sq_eq_self : rho * rho = 1 ∧ rho ≠ 1 := by
  constructor
  · ext x
    fin_cases x <;> rfl
  · decide

/-- `shiftC` has exact order three: neither it nor its square is the identity. -/
theorem shiftC_cube_eq_self :
    shiftC * shiftC * shiftC = 1 ∧ shiftC ≠ 1 ∧ shiftC * shiftC ≠ 1 := by
  constructor
  · ext x
    fin_cases x <;> rfl
  constructor <;> decide

/-- Reflection conjugates the three-cycle to its inverse, and the two
generators therefore do not commute in this concrete `Fin 3` action. -/
theorem rho_c_rho_eq_c_inv :
    rho * shiftC * rho = shiftC⁻¹ := by
  ext x
  fin_cases x <;> rfl

/-- The reflection and cycle act in an order-sensitive way: their products
send colour `0` to different colours. -/
theorem rho_shiftC_noncommute : rho * shiftC ≠ shiftC * rho := by
  intro h
  have h0 := congrArg (fun p : WeylA2 => p 0) h
  have hneq : (rho * shiftC) 0 ≠ (shiftC * rho) 0 := by decide
  exact hneq h0

end InfoGeometry.Canonical.A2WeylPermutationAction
