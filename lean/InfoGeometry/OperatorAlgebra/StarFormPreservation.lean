/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Units and infinitesimal operators preserving a star form

For an arbitrary associative star ring, the equation `star u * j * u = j`
defines a subgroup of the units. The infinitesimal equation
`star x * j + j * x = 0` defines an integer Lie subalgebra for the ordinary
ring commutator. Neither construction requires that `j` be invertible or
self-adjoint. They assert algebraic form preservation, without any positivity
or analytic interpretation.
-/

namespace InfoGeometry.OperatorAlgebra.StarFormPreservation

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B : Type*} [Ring B] [StarRing B]

/-- Units preserving the specified star form by congruence. -/
def preservingSubgroup (j : B) : Subgroup Bˣ where
  carrier := {u | star (u : B) * j * (u : B) = j}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change star (↑(u * v) : B) * j * (↑(u * v) : B) = j
    calc
      star (↑(u * v) : B) * j * (↑(u * v) : B) =
          star (v : B) * (star (u : B) * j * (u : B)) * (v : B) := by
        simp only [Units.val_mul, star_mul, mul_assoc]
      _ = j := by rw [hu, hv]
  inv_mem' := by
    intro u hu
    change star (↑u⁻¹ : B) * j * (↑u⁻¹ : B) = j
    calc
      star (↑u⁻¹ : B) * j * (↑u⁻¹ : B) =
          star (↑u⁻¹ : B) * (star (u : B) * j * (u : B)) * (↑u⁻¹ : B) := by
        rw [hu]
      _ = star ((u : B) * (↑u⁻¹ : B)) * j * ((u : B) * (↑u⁻¹ : B)) := by
        simp only [star_mul, mul_assoc]
      _ = j := by simp

@[simp]
theorem mem_preservingSubgroup (j : B) (u : Bˣ) :
    u ∈ preservingSubgroup j ↔ star (u : B) * j * (u : B) = j :=
  Iff.rfl

/-- Congruence preservation, exposed on the ambient ring. -/
theorem preserving_equation (j : B) (u : preservingSubgroup j) :
    star ((u : Bˣ) : B) * j * ((u : Bˣ) : B) = j :=
  u.property

/-- The form equation can also be written as an intertwining equation. -/
theorem star_mul_form_eq_form_mul_inv {j : B} {u : Bˣ}
    (hu : u ∈ preservingSubgroup j) :
    star (u : B) * j = j * (↑u⁻¹ : B) := by
  have h := congrArg (fun x : B => x * (↑u⁻¹ : B)) hu
  simpa only [mul_assoc, Units.mul_inv, mul_one] using h

/-- The infinitesimal star-form equation is closed under commutators. -/
theorem infinitesimal_commutator {j x y : B}
    (hx : star x * j + j * x = 0) (hy : star y * j + j * y = 0) :
    star (x * y - y * x) * j + j * (x * y - y * x) = 0 := by
  have hx' : star x * j = -(j * x) := eq_neg_of_add_eq_zero_left hx
  have hy' : star y * j = -(j * y) := eq_neg_of_add_eq_zero_left hy
  calc
    star (x * y - y * x) * j + j * (x * y - y * x) =
        star y * (star x * j) - star x * (star y * j) +
          j * (x * y - y * x) := by
      simp only [star_sub, star_mul]
      noncomm_ring
    _ = star y * (-(j * x)) - star x * (-(j * y)) +
          j * (x * y - y * x) := by rw [hx', hy']
    _ = -((star y * j) * x) + (star x * j) * y +
          j * (x * y - y * x) := by noncomm_ring
    _ = -(-(j * y) * x) + (-(j * x)) * y +
          j * (x * y - y * x) := by rw [hx', hy']
    _ = 0 := by noncomm_ring

/-- Infinitesimal form-preserving operators, with the native integer Lie structure. -/
def infinitesimalLieSubalgebra (j : B) : LieSubalgebra ℤ B where
  carrier := {x | star x * j + j * x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change star (x + y) * j + j * (x + y) = 0
    calc
      star (x + y) * j + j * (x + y) =
          (star x * j + j * x) + (star y * j + j * y) := by
        simp only [star_add, add_mul, mul_add]
        abel
      _ = 0 := by rw [hx, hy, add_zero]
  smul_mem' := by
    intro n x hx
    change star (n • x) * j + j * (n • x) = 0
    rw [star_zsmul, smul_mul_assoc, mul_smul_comm, ← smul_add, hx, smul_zero]
  lie_mem' := by
    intro x y hx hy
    change star (x * y - y * x) * j + j * (x * y - y * x) = 0
    exact infinitesimal_commutator hx hy

@[simp]
theorem mem_infinitesimalLieSubalgebra (j x : B) :
    x ∈ infinitesimalLieSubalgebra j ↔ star x * j + j * x = 0 :=
  Iff.rfl

end InfoGeometry.OperatorAlgebra.StarFormPreservation
