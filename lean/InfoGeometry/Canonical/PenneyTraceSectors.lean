/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PenneyOperatorEquation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Penney: traced right-isospin sector orthogonality

This is the finite matrix trace consequence of Penney (1971), equations
(98)–(101). It is not a conserved four-current: no derivatives or Lorentz
representation are present, and trace linearity alone does not give positivity.
-/

namespace InfoGeometry.Canonical.PenneyTraceSectors

open InfoGeometry.Canonical.PenneyOctonionIsospin

variable {R : Type*} [CommRing R] (n : Type*) [Fintype n] [DecidableEq n]
abbrev Mat := Matrix n n R

/-- Orthogonal right sectors have zero traced mixed product. -/
theorem trace_mixed_sector_zero (e f x : Mat n)
    (hfe : f * e = 0) :
    Matrix.trace (e * x * f) = 0 := by
  rw [Matrix.trace_mul_comm (e * x) f]
  rw [← mul_assoc, hfe, zero_mul, Matrix.trace_zero]

/-- A trace of two complementary idempotent sectors adds to the original trace. -/
theorem trace_right_sector_sum (e f x : Mat n) (h : e + f = 1) :
    Matrix.trace (x * e) + Matrix.trace (x * f) = Matrix.trace x := by
  rw [← map_add (Matrix.traceAddMonoidHom n R)]
  rw [← mul_add, h, mul_one]

/-- The matrix trace is unchanged by conjugation by a unit. -/
theorem trace_conjugation (u : (Mat n)ˣ) (x : Mat n) :
    Matrix.trace ((u : Mat n) * x * (↑u⁻¹ : Mat n)) =
      Matrix.trace x :=
  Matrix.trace_units_conj u x

end InfoGeometry.Canonical.PenneyTraceSectors
