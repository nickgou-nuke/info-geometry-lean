/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

/-!
# Algebraic precursor of the positive doubled-boundary Laplacian

Reuse the existing boundary, exchange, and componentwise lift operators.
The coefficients are arbitrary elements of an associative algebra.

For full real matrices with the positive Hilbert--Schmidt pairing, the
adjoint-identification theorem in LieJordanHodgeReal proves
  adjoint (boundary u) = swapOp * boundary (transpose u) * swapOp.
The theorem below is purely algebraic: it does not assume or assert this
identification, positivity, a spectral gap, or a Yang--Mills construction.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Exchanging the two blocks of the second boundary changes the quadratic
anticommutator from an inner derivation to Jordan multiplication. -/
theorem boundary_exchange_anticommutator (u v : A) :
    boundary (R := R) u * (swapOp * boundary (R := R) v * swapOp) +
      (swapOp * boundary (R := R) v * swapOp) * boundary (R := R) u =
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

/-- Algebraic block exchange. It becomes the metric adjoint only after
specializing the coefficient and proving the positive pairing law. -/
def coboundary (v : A) : Module.End R (A × A) :=
  swapOp * boundary (R := R) v * swapOp

@[simp] theorem coboundary_apply (v : A) (z : A × A) :
    coboundary (R := R) v z =
      (jordanLeft (R := R) v z.2, LieAlgebra.ad R A v z.1) := rfl

theorem boundary_coboundary (u v : A) :
    boundary (R := R) u * coboundary (R := R) v +
      coboundary (R := R) v * boundary (R := R) u =
        liftOp (jordanLeft (R := R) (u * v + v * u)) :=
  boundary_exchange_anticommutator u v

/-- A ring homomorphism transports the exchanged blocks without reordering them. -/
theorem map_coboundary {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (v : A) (z : A × A) :
    Prod.map f f (coboundary (R := R) v z) =
      coboundary (R := R) (f v) (Prod.map f f z) := by
  apply Prod.ext
  · change f (v * z.2 + z.2 * v) = f v * f z.2 + f z.2 * f v
    simp only [map_add, map_mul]
  · change f (v * z.1 - z.1 * v) = f v * f z.1 - f z.1 * f v
    simp only [map_sub, map_mul]

/-- The Jordan Hodge action, evaluated at the unit, need not vanish. -/
theorem jordan_quadratic_one (u v : A) :
    jordanLeft (R := R) (u * v + v * u) 1 = 2 • (u * v + v * u) := by
  change (u * v + v * u) * 1 + 1 * (u * v + v * u) = _
  simp only [mul_one, one_mul, two_nsmul]

end InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
