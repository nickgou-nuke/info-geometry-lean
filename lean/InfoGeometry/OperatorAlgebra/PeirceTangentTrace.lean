/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentTangent
import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic cancellation for idempotent tangent products

An additive cyclic functional annihilates an idempotent tangent and the
ordered product of three such tangents. The proof reuses the existing
off-diagonal decomposition and the existing directed-corner trace theorem.
It works in an arbitrary associative ring, without division by two or
self-adjointness assumptions.

This is the finite algebraic cancellation appearing in projector-curvature
closure calculations. Parameter derivatives, differential-form closure,
Kato transport, determinant-line holonomy, and convergence under lattice
refinement require additional constructions and are not asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceTangentTrace

open InfoGeometry.Core.PeirceTangent
open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

variable {A S : Type*} [Ring A] [AddCommGroup S]

/-- Every first-order idempotent tangent has zero value under an additive
cyclic functional. The directed-corner theorem supplies both cancellations. -/
theorem cyclicFunctional_tangent_eq_zero
    (τ : A →+ S) (hτ : IsCyclic τ) {p x : A}
    (hp : p * p = p) (hx : p * x + x * p = x) :
    τ x = 0 := by
  have hdecomp := tangent_eq_offDiagonal hp hx
  have hcorners := cyclicFunctional_directedCorners_eq_zero τ hτ hp x
  calc
    τ x = τ (p * x * (1 - p) + (1 - p) * x * p) :=
      congrArg τ hdecomp
    _ = 0 := by rw [map_add, hcorners.1, hcorners.2, add_zero]

/-- Three ordered tangent factors again satisfy the first-order idempotent
equation, so their cyclic value vanishes. Their pairwise products need not
commute, and the individual factors need not be self-adjoint. -/
theorem cyclicFunctional_tangent_mul_mul_eq_zero
    (τ : A →+ S) (hτ : IsCyclic τ) {p x y z : A}
    (hp : p * p = p)
    (hx : p * x + x * p = x)
    (hy : p * y + y * p = y)
    (hz : p * z + z * p = z) :
    τ (x * y * z) = 0 := by
  have hxyz : p * (x * y * z) + (x * y * z) * p = x * y * z := by
    calc
      p * (x * y * z) + (x * y * z) * p =
          (p * x + x * p - x) * y * z -
            x * (p * y + y * p - y) * z +
            x * y * (p * z + z * p - z) + x * y * z := by
              noncomm_ring
      _ = x * y * z := by rw [hx, hy, hz]; simp
  exact cyclicFunctional_tangent_eq_zero τ hτ hp hxyz

/-- The alternating triple term used in projector-curvature calculations
vanishes before any differential or integration argument is invoked. -/
theorem cyclicFunctional_tangent_commutator_eq_zero
    (τ : A →+ S) (hτ : IsCyclic τ) {p x y z : A}
    (hp : p * p = p)
    (hx : p * x + x * p = x)
    (hy : p * y + y * p = y)
    (hz : p * z + z * p = z) :
    τ (x * (y * z - z * y)) = 0 := by
  rw [mul_sub, ← mul_assoc, ← mul_assoc, map_sub,
    cyclicFunctional_tangent_mul_mul_eq_zero τ hτ hp hx hy hz,
    cyclicFunctional_tangent_mul_mul_eq_zero τ hτ hp hx hz hy,
    sub_self]

/-- Native finite matrix trace is cyclic over commutative coefficients.
The matrix algebra remains noncommutative, and the factor order is retained. -/
theorem trace_tangent_mul_mul_eq_zero
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {p x y z : Matrix n n R}
    (hp : p * p = p)
    (hx : p * x + x * p = x)
    (hy : p * y + y * p = y)
    (hz : p * z + z * p = z) :
    Matrix.trace (x * y * z) = 0 := by
  exact cyclicFunctional_tangent_mul_mul_eq_zero
    (Matrix.traceAddMonoidHom n R)
    (fun a b => Matrix.trace_mul_comm a b) hp hx hy hz

end InfoGeometry.OperatorAlgebra.PeirceTangentTrace
