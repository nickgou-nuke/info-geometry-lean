/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Two trace pairings on the full matrix algebra

The bilinear pairing `trace (A * B)` and the sesquilinear pairing
`trace (star A * B)` have different adjoint conventions. We use the native
associative Lie bracket and native unitary star-algebra automorphism.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixTraceGeometry

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Cyclic integration by parts for the bilinear trace pairing. -/
theorem trace_lie_mul (H A B : Matrix n n ℂ) :
    trace (⁅H, A⁆ * B) = -trace (A * ⁅H, B⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, trace_sub, mul_assoc]
  rw [trace_mul_comm H (A * B)]
  simp only [mul_assoc]
  abel

/-- The Hilbert--Schmidt adjoint of `ad H` is `ad (star H)`.
This identity is stated directly in the trace pairing, without changing
the ambient matrix norm or installing an inner-product instance. -/
theorem trace_star_lie (H A B : Matrix n n ℂ) :
    trace (star ⁅H, A⁆ * B) = trace (star A * ⁅star H, B⁆) := by
  simp only [Ring.lie_def, star_sub, star_mul, sub_mul, mul_sub, trace_sub, mul_assoc]
  rw [trace_mul_comm (star H) (star A * B)]
  simp only [mul_assoc]

/-- A Hermitian generator gives a self-adjoint commutator superoperator
for the Hilbert--Schmidt pairing. -/
theorem trace_star_lie_of_isSelfAdjoint {H : Matrix n n ℂ}
    (hH : IsSelfAdjoint H) (A B : Matrix n n ℂ) :
    trace (star ⁅H, A⁆ * B) = trace (star A * ⁅H, B⁆) := by
  rw [trace_star_lie, hH.star_eq]

/-- A skew-Hermitian generator gives a skew-adjoint commutator
superoperator for the Hilbert--Schmidt pairing. -/
theorem trace_star_lie_of_star_eq_neg {H : Matrix n n ℂ}
    (hH : star H = -H) (A B : Matrix n n ℂ) :
    trace (star ⁅H, A⁆ * B) = -trace (star A * ⁅H, B⁆) := by
  rw [trace_star_lie, hH, neg_lie, mul_neg, trace_neg]

/-- Unitary conjugation preserves the cyclic trace. -/
theorem trace_conjStarAlgAut (u : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    trace (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A) = trace A := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [trace_mul_cycle]
  simp

/-- Native unitary conjugation is an isometry for the Hilbert--Schmidt pairing. -/
theorem trace_star_conjStarAlgAut (u : unitary (Matrix n n ℂ))
    (A B : Matrix n n ℂ) :
    trace (star (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A) *
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u B) = trace (star A * B) := by
  rw [← map_star, ← map_mul]
  exact trace_conjStarAlgAut u _

end InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
