/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.DiracSuperalgebra

/-!
# Algebraic tangent equations for idempotents

The equation `p*x + x*p = x` is the first-order idempotent equation.
It characterizes off-diagonal Peirce directions without assumptions on two.
This module does not construct a manifold. For self-adjoint projection
deformations, self-adjointness of the direction is an additional condition.
-/

namespace InfoGeometry.Core.PeirceTangent

variable {R : Type*} [Ring R]

/-- The first-order idempotent equation is equivalent to both diagonal
Peirce corners vanishing, even in characteristic two. -/
theorem tangent_iff_diagonal_corners_zero {p x : R} (hp : p * p = p) :
    p * x + x * p = x ↔
      p * x * p = 0 ∧ (1 - p) * x * (1 - p) = 0 := by
  constructor
  · intro hx
    have hpxp : p * x * p = 0 := by
      have hleft := congrArg (fun y => p * y) hx
      rw [mul_add, ← mul_assoc p p x, hp, ← mul_assoc p x p] at hleft
      exact add_left_cancel (hleft.trans (add_zero (p * x)).symm)
    refine ⟨hpxp, ?_⟩
    calc
      (1 - p) * x * (1 - p) = x - (p * x + x * p) + p * x * p := by
        noncomm_ring
      _ = 0 := by rw [hx, hpxp]; abel
  · rintro ⟨hpxp, hqxq⟩
    calc
      p * x + x * p = x + p * x * p - (1 - p) * x * (1 - p) := by
        noncomm_ring
      _ = x := by rw [hpxp, hqxq]; abel

/-- A tangent direction is the sum of its two off-diagonal corners. -/
theorem tangent_eq_offDiagonal {p x : R} (hp : p * p = p)
    (hx : p * x + x * p = x) :
    x = p * x * (1 - p) + (1 - p) * x * p := by
  have hpxp := ((tangent_iff_diagonal_corners_zero hp).mp hx).1
  calc
    x = p * x + x * p - (p * x * p + p * x * p) := by rw [hx, hpxp]; abel
    _ = p * x * (1 - p) + (1 - p) * x * p := by noncomm_ring

/-- Reflection anticommutation measures twice the tangent-equation defect.
Its vanishing cannot be cancelled to tangency in a general ring. -/
theorem reflection_anticommutator (p x : R) :
    (2 * p - 1) * x + x * (2 * p - 1) = 2 • (p * x + x * p - x) := by
  rw [two_nsmul]
  noncomm_ring

/-- Over a ring where doubling is injective, anticommutation with the
reflection `2 * p - 1` is equivalent to the first-order Grassmannian
tangent equation.  The injectivity hypothesis is necessary: in
characteristic two the reflection identity only sees twice the tangent
defect. -/
theorem tangent_iff_reflection_anticommutes_of_two_smul_injective
    {p x : R} (h_two : Function.Injective (fun y : R => (2 : ℕ) • y)) :
    p * x + x * p = x ↔
      (2 * p - 1) * x + x * (2 * p - 1) = 0 := by
  constructor
  · intro hx
    rw [reflection_anticommutator, hx, sub_self, smul_zero]
  · intro h_reflection
    rw [reflection_anticommutator] at h_reflection
    apply sub_eq_zero.mp
    apply h_two
    simpa using h_reflection

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable [StarRing R]

/-- Every linear combination of the two MP arrows with signs `+` is an
algebraic tangent direction at the exact support. No adjoint duality is used. -/
theorem exactSupport_tangent_majoranaPlus {a m : R}
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    exactSupport a m * majoranaPlus a m +
      majoranaPlus a m * exactSupport a m = majoranaPlus a m := by
  rcases partial_matrix_unit_identities h ha with
    ⟨⟨hpa, _, hap, _⟩, ⟨_, hmp, _, hpm⟩, _⟩
  simp only [majoranaPlus, mul_add, add_mul, hpa, hap, hmp, hpm,
    add_zero, zero_add]

/-- The skew combination also solves the algebraic tangent equation;
it need not be a self-adjoint tangent direction. -/
theorem exactSupport_tangent_majoranaMinus {a m : R}
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    exactSupport a m * majoranaMinus a m +
      majoranaMinus a m * exactSupport a m = majoranaMinus a m := by
  rcases partial_matrix_unit_identities h ha with
    ⟨⟨hpa, _, hap, _⟩, ⟨_, hmp, _, hpm⟩, _⟩
  unfold majoranaMinus
  calc
    exactSupport a m * (a - m) + (a - m) * exactSupport a m =
        (exactSupport a m * a + a * exactSupport a m) -
          (exactSupport a m * m + m * exactSupport a m) := by
            noncomm_ring
    _ = a - m := by rw [hpa, hap, hpm, hmp]; abel

end InfoGeometry.Core.PeirceTangent
