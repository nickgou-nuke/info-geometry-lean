/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

/-!
# The exchanged boundary and its exact Jordan Hodge operator

No adjoint, positivity, or gap is inferred at the ring level. The real matrix
consumer supplies the positive adjoint. This keeps the previous derivation-
valued anticommutator distinct from the exchanged, Jordan-valued one.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Exchange the two boundary blocks. Positivity is not part of this definition. -/
def coboundary (v : A) : Module.End R (A × A) :=
  swapOp * boundary (R := R) v * swapOp

@[simp] theorem coboundary_apply (v : A) (z : A × A) :
    coboundary (R := R) v z =
      (jordanLeft (R := R) v z.2, LieAlgebra.ad R A v z.1) := rfl

/-- The exchanged anticommutator retains the full quadratic coefficient. -/
theorem boundary_coboundary_anticommutator (u v : A) :
    boundary (R := R) u * coboundary (R := R) v +
      coboundary (R := R) v * boundary (R := R) u =
        liftOp (jordanLeft (R := R) (u * v + v * u)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change (u * (v * z.1 - z.1 * v) - (v * z.1 - z.1 * v) * u) +
      (v * (u * z.1 + z.1 * u) + (u * z.1 + z.1 * u) * v) =
      (u * v + v * u) * z.1 + z.1 * (u * v + v * u)
    noncomm_ring
  · change (u * (v * z.2 + z.2 * v) + (v * z.2 + z.2 * v) * u) +
      (v * (u * z.2 - z.2 * u) - (u * z.2 - z.2 * u) * v) =
      (u * v + v * u) * z.2 + z.2 * (u * v + v * u)
    noncomm_ring

/-- The exchanged operator has the same coefficient-square obstruction. -/
theorem coboundary_sq (v : A) :
    coboundary (R := R) v * coboundary (R := R) v =
      liftOp (LieAlgebra.ad R A (v * v)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change v * (v * z.1 - z.1 * v) + (v * z.1 - z.1 * v) * v =
      (v * v) * z.1 - z.1 * (v * v)
    noncomm_ring
  · change v * (v * z.2 + z.2 * v) - (v * z.2 + z.2 * v) * v =
      (v * v) * z.2 - z.2 * (v * v)
    noncomm_ring

theorem coboundary_square_zero {v : A} (hv : v * v = 0) :
    coboundary (R := R) v * coboundary (R := R) v = 0 := by
  rw [coboundary_sq, hv]
  apply LinearMap.ext
  intro z
  change (0 * z.1 - z.1 * 0, 0 * z.2 - z.2 * 0) = (0, 0)
  simp

/-- Nilpotence gives commutation with the Hodge operator, not a gap. -/
theorem boundary_commutes_hodge {u : A} (hu : u * u = 0) (v : A) :
    boundary (R := R) u * liftOp (jordanLeft (R := R) (u * v + v * u)) =
      liftOp (jordanLeft (R := R) (u * v + v * u)) * boundary (R := R) u := by
  rw [← boundary_coboundary_anticommutator]
  have hd := boundary_square_zero (R := R) hu
  simp only [mul_add, add_mul, ← mul_assoc, hd, zero_mul, zero_add]
  simp only [mul_assoc, hd, mul_zero, add_zero]

/-- Its value on the identity pair need not be zero. -/
theorem hodge_identity_pair (u v : A) :
    liftOp (jordanLeft (R := R) (u * v + v * u)) (1, 1) =
      ((2 : ℕ) • (u * v + v * u), (2 : ℕ) • (u * v + v * u)) := by
  change ((u * v + v * u) * 1 + 1 * (u * v + v * u),
    (u * v + v * u) * 1 + 1 * (u * v + v * u)) = _
  simp only [mul_one, one_mul, two_nsmul]

end InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
