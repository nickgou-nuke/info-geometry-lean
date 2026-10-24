/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.OperatorAlgebra.TracialCARDensity

/-! Exact centralizer and fixed-point boundaries for native finite weighted traces.
Trace separation is Mathlib's existing matrix theorem. No positivity, nonempty
index type, new state construction, or analytic KMS assertion is needed here.
-/

namespace InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

section Algebraic
variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- An invertible weight preserves separation of the right argument.
This is algebraic nondegeneracy, not a positivity hypothesis. -/
theorem trace_unit_right_annihilation_iff (u : (Matrix n n R)ˣ) (Z : Matrix n n R) :
    (∀ Y : Matrix n n R, Matrix.trace ((u : Matrix n n R) * (Y * Z)) = 0) ↔
      Z = 0 := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro T
    simpa only [← mul_assoc, Units.mul_inv, one_mul, mul_zero, Matrix.trace_zero] using
      h ((↑(u⁻¹) : Matrix n n R) * T)
  · rintro rfl Y
    simp
end Algebraic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- All tested commutators vanish precisely on the density centralizer.
The density may be singular and need not be positive. -/
theorem weightedTrace_commutator_zero_iff (D X : Matrix n n ℂ) :
    (∀ Y : Matrix n n ℂ, weightedTrace D (X * Y - Y * X) = 0) ↔ Commute D X := by
  have hdef (Y : Matrix n n ℂ) :
      weightedTrace D (X * Y - Y * X) = Matrix.trace ((D * X - X * D) * Y) := by
    exact InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted_commutator_defect
      ⟨Matrix.traceLinearMap n ℂ ℂ, fun A B => Matrix.trace_mul_comm A B⟩ D X Y
  constructor
  · intro h
    change D * X = X * D
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    have hY := h Y
    rw [hdef Y, sub_mul, Matrix.trace_sub] at hY
    exact sub_eq_zero.mp hY
  · intro h Y
    rw [hdef Y, h.eq, sub_self, zero_mul,
      Matrix.trace_zero]

/-- Testing the native modular defect against every right factor forces a fixed point.
In particular, global defect annihilation is stronger than the unit KMS identity. -/
theorem weightedTrace_unit_defect_zero_iff (u : (Matrix n n ℂ)ˣ) (X : Matrix n n ℂ) :
    (∀ Y : Matrix n n ℂ,
      weightedTrace (u : Matrix n n ℂ) (Y * (unitImaginaryTimeAlgEquiv u X - X)) = 0) ↔
        unitImaginaryTimeAlgEquiv u X = X := by
  change (∀ Y : Matrix n n ℂ,
    Matrix.trace ((u : Matrix n n ℂ) * (Y * (unitImaginaryTimeAlgEquiv u X - X))) = 0) ↔ _
  rw [trace_unit_right_annihilation_iff, sub_eq_zero]

end InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
