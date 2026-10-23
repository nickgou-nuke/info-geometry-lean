/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Unnormalized associative-envelope identities over rings

These identities use `x*y + y*x`, without division by two. The normalized
real-algebra Jordan product remains owned by `JordanPeirceDecomposition`.
No bundled Jordan or Kantor triple-system structure is asserted here.
-/
namespace InfoGeometry.Core.JordanAssociator

variable {R : Type*} [Ring R]

/-- The unnormalized symmetrized-product associator is a double commutator. -/
theorem symm_associator_eq_double_commutator (x y z : R) :
    ((x * y + y * x) * z + z * (x * y + y * x)) -
      (x * (y * z + z * y) + (y * z + z * y) * x) =
        y * (x * z - z * x) - (x * z - z * x) * y := by
  noncomm_ring

/-- The correct triple expansion has a left multiplication by `z` in its correction. -/
theorem symm_triple_eq_symm_sub_commutator (x y z : R) :
    x * y * z + z * y * x =
      (x * y) * z + z * (x * y) - z * (x * y - y * x) := by
  noncomm_ring

/-- Exact obstruction to the alternate triple expansion proposed in the source note. -/
theorem proposed_triple_formula_defect (x y z : R) :
    ((x * y) * z + z * (x * y) - (x * (z * y) - (z * y) * x)) -
      (x * y * z + z * y * x) = (z * x - x * z) * y := by
  noncomm_ring

/-- Square-zero and an inner inverse suffice for the unnormalized `-2d` law;
neither an involution nor the other Moore–Penrose equations are needed. -/
theorem symm_associator_square_zero_inner_inverse {d b : R}
    (hd : d * d = 0) (hinner : d * b * d = d) :
    ((d * d + d * d) * b + b * (d * d + d * d)) -
      (d * (d * b + b * d) + (d * b + b * d) * d) = -(2 • d) := by
  rw [symm_associator_eq_double_commutator]
  calc
    _ = (d * d) * b - (d * b * d + d * b * d) + b * (d * d) := by
      noncomm_ring
    _ = -(2 • d) := by rw [hd, hinner]; simp [two_mul]

end InfoGeometry.Core.JordanAssociator
