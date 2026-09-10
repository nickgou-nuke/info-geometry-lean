import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.EmergentKillingField

Finite-dimensional operator-level Killing identity for the trace-form metric.
-/

namespace InfoGeometry.Canonical.EmergentKillingField

open Matrix

abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Trace on `2×2` real matrices. -/
def tr (A : M2R) : ℝ := A 0 0 + A 1 1

/-- Trace-form metric. -/
def traceForm (A B : M2R) : ℝ := tr (A * B)

/-- Trace of a commutator vanishes. -/
theorem trace_commutator_zero (A B : M2R) :
    tr (A * B - B * A) = 0 := by
  unfold tr
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Trace cyclicity in `2×2`: `tr (A * B) = tr (B * A)`. -/
theorem tr_mul_comm (A B : M2R) :
    tr (A * B) = tr (B * A) := by
  have h := trace_commutator_zero A B
  have : tr (A * B) - tr (B * A) = 0 := by
    simpa [tr, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  linarith

/-- Scalar compatibility of the concrete `2×2` trace. -/
theorem tr_smul (c : ℝ) (A : M2R) :
    tr (c • A) = c * tr A := by
  unfold tr
  simp
  ring

/--
Finite `2×2` modular spectral selection rule: a nonzero commutator eigenmode
has zero concrete trace.
-/
theorem modular_spectral_selection_rule (H X : M2R) (lam : ℝ)
    (hEig : H * X - X * H = lam • X) (hlam : lam ≠ 0) :
    tr X = 0 := by
  have htr_comm : tr (H * X - X * H) = 0 := trace_commutator_zero H X
  have h : lam * tr X = 0 := by
    rw [← tr_smul lam X, ← hEig]
    exact htr_comm
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hlam h

/--
Operator Killing equation for the commutator flow and trace-form metric.
-/
theorem emergent_killing_equation (X A B : M2R) :
    traceForm (X * A - A * X) B + traceForm A (X * B - B * X) = 0 := by
  unfold traceForm tr
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end InfoGeometry.Canonical.EmergentKillingField
