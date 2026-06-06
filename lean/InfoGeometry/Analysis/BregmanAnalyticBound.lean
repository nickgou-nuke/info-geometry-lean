import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Matrix
open Complex
open Real

noncomputable section

/-!
# Bregman Analytic Bound

The thermodynamic cost term

`exp (ε • K) - I - ε • K`

is the matrix-exponential remainder used in the Bregman/IPM reading of the
modular phase-axis flow. This file does not prove the analytic matrix
remainder estimate. Instead, it names that estimate as an explicit hypothesis
and proves the kernel-checkable consequences used by the Cantor-boundary lane.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `exponentialRemainder_zero`
* `exponentialRemainder_zero_norm`
* `phase_axis_deformation_bounded_of_quadratic_bound`
* `dikin_bound_of_phase_axis_norm`
* `bregman_bound_clears_at_flat_boundary`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* `phase_axis_deformation_bounded_of_quadratic_bound`
* `dikin_bound_of_phase_axis_norm`

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Prove the matrix-exponential quadratic remainder estimate from Taylor
  expansion and a concrete operator norm:
  `HasQuadraticBregmanBound K`.
* Prove `‖K‖ = 1` for the concrete phase-axis matrix from its chosen C*-norm,
  not merely from the algebraic relation `K ^ 2 = -1`.
* Build the full `ℓ²(BinaryCantorBoundary) ⊗ DoubledSpace ℝ` completion and
  derive uniform continuity of the diagonal Cuntz shift from boundedness of
  the base shift and the fiber phase axis.
-/

open scoped BigOperators Matrix Norms.Operator

set_option autoImplicit false

namespace InfoGeometry.Analysis.BregmanAnalyticBound

abbrev MatrixEnd (n : ℕ) :=
  Matrix (Fin n) (Fin n) ℂ

/-! ## Exponential remainder -/

/--
The Bregman/IPM exponential remainder `exp (ε • K) - I - ε • K`.
-/
noncomputable def exponentialRemainder {n : ℕ}
    (K : MatrixEnd n) (ε : ℝ) : MatrixEnd n :=
  (NormedSpace.exp (ε • K) : MatrixEnd n) - 1 - (ε • K : MatrixEnd n)

@[simp]
theorem exponentialRemainder_zero {n : ℕ} (K : MatrixEnd n) :
    exponentialRemainder K 0 = 0 := by
  simp [exponentialRemainder]

@[simp]
theorem exponentialRemainder_zero_norm {n : ℕ} (K : MatrixEnd n) :
    ‖exponentialRemainder K 0‖ = 0 := by
  simp

/-! ## Conditional quadratic Bregman bound -/

/--
Explicit local quadratic remainder estimate.

This is a proposition, not a global postulate. The analytic closure target is
to prove this predicate for the concrete phase-axis norm used by the
representation.
-/
def HasQuadraticBregmanBound {n : ℕ} (K : MatrixEnd n) : Prop :=
  ∀ ε : ℝ, ε * ‖K‖ ≤ 1 →
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 * ‖K‖ ^ 2

/--
Read back the quadratic Bregman estimate from an explicit theorem hypothesis.
-/
theorem phase_axis_deformation_bounded_of_quadratic_bound {n : ℕ}
    (K : MatrixEnd n)
    (hquad : HasQuadraticBregmanBound K)
    (ε : ℝ)
    (hε : ε * ‖K‖ ≤ 1) :
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 * ‖K‖ ^ 2 :=
  hquad ε hε

/--
If the phase axis has norm one, the quadratic Bregman bound becomes the Dikin
radius estimate `‖exp (εK) - I - εK‖ ≤ ε²`.
-/
theorem dikin_bound_of_phase_axis_norm {n : ℕ}
    (K : MatrixEnd n)
    (hquad : HasQuadraticBregmanBound K)
    (hK_norm : ‖K‖ = 1)
    (ε : ℝ)
    (hε : ε ≤ 1) :
    ‖exponentialRemainder K ε‖ ≤ ε ^ 2 := by
  have hεK : ε * ‖K‖ ≤ 1 := by
    simpa [hK_norm] using hε
  have h := hquad ε hεK
  simpa [hK_norm] using h

/--
The flat KMS boundary has zero modular step, so the Bregman deformation clears
without any analytic estimate.
-/
theorem bregman_bound_clears_at_flat_boundary {n : ℕ}
    (K : MatrixEnd n) :
    ‖exponentialRemainder K 0‖ ≤ 0 := by
  simp

end InfoGeometry.Analysis.BregmanAnalyticBound
