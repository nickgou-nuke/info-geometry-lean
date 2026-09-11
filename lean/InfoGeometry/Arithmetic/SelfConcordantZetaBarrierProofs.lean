import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Proof layer for the zeta-barrier discussion

No sockets. No certificates. No axioms. No `sorry`.

This file proves three finite algebraic facts:

1. The Cayley unit-circle equation is exactly the critical-line equation.
2. The canonical logarithmic barrier has the sharp one-dimensional
   Nesterov--Nemirovski cubic bound.
3. The proposed real bosonic zeta Massieu sign `-log Z` is not an NN barrier;
   already one Euler mode has negative second derivative. Even with the convex
   sign `+log Z`, one Euler mode fails the standard constant-2 NN bound in the
   inverse-temperature coordinate.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs

/-! ## 1. Cayley equation -/

/-- Algebraic unit-circle equation obtained from `|(s - 1) / s| = 1`
for `s = σ + it`, after clearing the common denominator. -/
def CayleyUnitEquation (σ t : ℝ) : Prop :=
  (σ - 1) ^ 2 + t ^ 2 = σ ^ 2 + t ^ 2

/-- The Cayley unit-circle equation is exactly the critical-line equation. -/
theorem cayleyUnitEquation_iff_critical (σ t : ℝ) :
    CayleyUnitEquation σ t ↔ σ = (1 : ℝ) / 2 := by
  unfold CayleyUnitEquation
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-! ## 2. Nesterov--Nemirovski square-form bound -/

/-- One-dimensional square-form NN inequality. -/
def NNBoundSq (d2 d3 : ℝ) : Prop :=
  0 ≤ d2 ∧ d3 ^ 2 ≤ 4 * d2 ^ 3

/--
The canonical barrier `f(x) = -log x` has
`f''(x) = x⁻¹ ^ 2` and `f'''(x) = -2 * x⁻¹ ^ 3`.
For these derivative values the NN inequality is sharp.
-/
theorem canonicalLogBarrier_NN_algebraic (x : ℝ) :
    NNBoundSq (x⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) := by
  constructor
  · exact sq_nonneg x⁻¹
  · have h : (-2 * x⁻¹ ^ 3) ^ 2 = 4 * (x⁻¹ ^ 2) ^ 3 := by
      ring
    rw [h]

/-- The sharp cubic equality for the canonical logarithmic barrier. -/
theorem canonicalLogBarrier_cubic_equality (x : ℝ) :
    (-2 * x⁻¹ ^ 3) ^ 2 = 4 * (x⁻¹ ^ 2) ^ 3 := by
  ring

/-! ## 3. Sign obstruction for `-log Z` -/

/-- A negative Hessian slot immediately rules out an NN barrier. -/
theorem negative_hessian_not_NN {d2 d3 : ℝ} (h : d2 < 0) :
    ¬ NNBoundSq d2 d3 := by
  intro H
  exact not_le_of_gt h H.1

/--
For a single bosonic Euler mode with energy `E > 0` and
`q = exp (-βE)` satisfying `0 < q < 1`, the real Massieu sign

`Φ_E(β) = log (1 - exp (-βE)) = -log ((1 - exp (-βE))⁻¹)`

has second derivative

`Φ_E''(β) = - E^2 q / (1 - q)^2`,

which is strictly negative.
-/
theorem negLogEulerMode_secondSlot_negative
    (E q : ℝ) (hE : 0 < E) (hq0 : 0 < q) (hq1 : q < 1) :
    -(E ^ 2 * q) / (1 - q) ^ 2 < 0 := by
  have hE2 : 0 < E ^ 2 := sq_pos_of_pos hE
  have hnum : 0 < E ^ 2 * q := mul_pos hE2 hq0
  have hbase : 0 < 1 - q := by linarith
  have hden : 0 < (1 - q) ^ 2 := sq_pos_of_pos hbase
  have hnumneg : -(E ^ 2 * q) < 0 := neg_neg_of_pos hnum
  exact div_neg_of_neg_of_pos hnumneg hden

/-- Therefore a single real bosonic Euler mode with the sign `-log Z`
cannot satisfy the NN barrier condition. -/
theorem negLogEulerMode_not_NN
    (E q d3 : ℝ) (hE : 0 < E) (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ NNBoundSq (-(E ^ 2 * q) / (1 - q) ^ 2) d3 := by
  exact negative_hessian_not_NN
    (negLogEulerMode_secondSlot_negative E q hE hq0 hq1)

/-- Hence the proposed real sign `-log ζ` cannot be proved as an NN barrier
by reducing to bosonic Euler factors; the one-factor Hessian is already negative. -/
theorem proposed_negLogZetaBarrier_sign_obstructed
    (E q d3 : ℝ) (hE : 0 < E) (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ NNBoundSq (-(E ^ 2 * q) / (1 - q) ^ 2) d3 :=
  negLogEulerMode_not_NN E q d3 hE hq0 hq1

/-! ## 4. Constant-2 obstruction for the convex sign `+log Z` -/

/--
For `0 < q < 1`, the cleared NN inequality for the convex one-mode Euler
barrier fails strictly:

`4 q^3 < q^2 (1+q)^2`.
-/
theorem logEulerMode_NN_core_fails (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    4 * q ^ 3 < q ^ 2 * (1 + q) ^ 2 := by
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hq2_pos : 0 < q ^ 2 := sq_pos_of_ne_zero hq_ne
  have h1q_ne : 1 - q ≠ 0 := by
    nlinarith
  have h1q2_pos : 0 < (1 - q) ^ 2 := sq_pos_of_ne_zero h1q_ne
  have hpos : 0 < q ^ 2 * (1 - q) ^ 2 := mul_pos hq2_pos h1q2_pos
  have hdiff : q ^ 2 * (1 + q) ^ 2 - 4 * q ^ 3 = q ^ 2 * (1 - q) ^ 2 := by
    ring
  have hdiff_pos : 0 < q ^ 2 * (1 + q) ^ 2 - 4 * q ^ 3 := by
    simpa [hdiff] using hpos
  linarith

/--
After multiplying by the positive factor `E^6`, the same strict reverse
inequality is the cleared derivative inequality for
`f(β) = -log (1 - exp(-βE)) = +log Z_E(β)`.
-/
theorem logEulerMode_NN_cleared_derivative_bound_fails
    (E q : ℝ) (hE : 0 < E) (hq0 : 0 < q) (hq1 : q < 1) :
    4 * (E ^ 2 * q) ^ 3 < (E ^ 3 * q * (1 + q)) ^ 2 := by
  have hcore := logEulerMode_NN_core_fails q hq0 hq1
  have hE6_pos : 0 < E ^ 6 := by positivity
  have hmul := mul_lt_mul_of_pos_left hcore hE6_pos
  nlinarith

end InfoGeometry.Arithmetic.SelfConcordantZetaBarrierProofs
