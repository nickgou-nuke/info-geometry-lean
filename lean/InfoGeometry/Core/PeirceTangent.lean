/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.IdempotentTangent
import InfoGeometry.Core.DiracSuperalgebra

/-!
# Algebraic tangent equations for idempotents

The equation `p*x + x*p = x` is the first-order idempotent equation.
It characterizes off-diagonal Peirce directions without assumptions on two.
This module does not construct a manifold. For self-adjoint projection
deformations, self-adjointness of the direction is an additional condition.
-/

namespace InfoGeometry.Core.PeirceTangent

variable {R : Type*} [Ring R] [StarRing R]

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

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
