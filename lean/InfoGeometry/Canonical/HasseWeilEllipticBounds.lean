import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Elliptic Hasse--Weil Trace Bounds

This file records scalar algebraic consequences of the elliptic Hasse trace
inequality.  It does not construct an elliptic curve, Frobenius, étale
cohomology, or a Weil proof of the trace inequality; the trace-square bound is
an explicit theorem hypothesis.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `q_nonneg_of_trace_sq_le`, `hasse_bound_abs_of_trace_sq_le`,
  `ellipticPointCountOne`, `hasse_point_count_bound_of_trace_sq_le`,
  `hasse_weil_rat_identity`, `elliptic_trace_point_count_sq_bound`,
  `characteristic_poly_roots`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  The Hasse absolute-value and point-count bounds are conditional on the
  explicit scalar trace inequality `(α + β)^2 ≤ 4 * q`.
- BUCKET 3: OPEN CLOSURE DEBT:
  The geometric theorem producing the trace inequality from an elliptic curve
  over a finite field is not asserted here.
-/

namespace InfoGeometry.Canonical.HasseWeilEllipticBounds

/--
The field-size parameter is nonnegative whenever the trace-square inequality
`(α + β)^2 ≤ 4q` holds.
-/
theorem q_nonneg_of_trace_sq_le (q α β : ℝ)
    (htrace : (α + β) ^ 2 ≤ 4 * q) :
    0 ≤ q := by
  have hmul : 0 ≤ 4 * q := (sq_nonneg (α + β)).trans htrace
  nlinarith

/--
The Hasse trace bound as a scalar consequence of the trace-square inequality:
`|α + β| ≤ 2√q`.
-/
theorem hasse_bound_abs_of_trace_sq_le (q α β : ℝ)
    (htrace : (α + β) ^ 2 ≤ 4 * q) :
    |α + β| ≤ 2 * Real.sqrt q := by
  have hsqrt := Real.sqrt_le_sqrt htrace
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))] at hsqrt
  have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hsqrt_four] at hsqrt
  exact hsqrt

/-- The one-step elliptic point count encoded by Frobenius trace data. -/
def ellipticPointCountOne (q α β : ℝ) : ℝ :=
  q + 1 - (α + β)

/--
The one-step point-count form of the Hasse bound:
`|N₁ - (q + 1)| ≤ 2√q`.
-/
theorem hasse_point_count_bound_of_trace_sq_le (q α β : ℝ)
    (htrace : (α + β) ^ 2 ≤ 4 * q) :
    |ellipticPointCountOne q α β - (q + 1)| ≤ 2 * Real.sqrt q := by
  have h_eq : ellipticPointCountOne q α β - (q + 1) = -(α + β) := by
    unfold ellipticPointCountOne
    ring
  rw [h_eq, abs_neg]
  exact hasse_bound_abs_of_trace_sq_le q α β htrace

/--
The trace-square bound is equivalent to the same square bound on the rational
point-count deviation when `N₁ = q + 1 - a`.
-/
theorem hasse_weil_rat_identity (q a N₁ : ℚ)
    (hN : N₁ = q + 1 - a) :
    a ^ 2 ≤ 4 * q ↔ (N₁ - (q + 1)) ^ 2 ≤ 4 * q := by
  have h_eq : N₁ - (q + 1) = -a := by
    rw [hN]
    ring
  rw [h_eq]
  ring_nf

/--
The rational point-count deviation square bound obtained directly from the
trace-square bound.
-/
theorem elliptic_trace_point_count_sq_bound (q α β : ℚ)
    (htrace : (α + β) ^ 2 ≤ 4 * q) :
    let a := α + β
    let N₁ := q + 1 - a
    (N₁ - (q + 1)) ^ 2 ≤ 4 * q := by
  intro a N₁
  have h_eq : N₁ - (q + 1) = -a := by
    dsimp [N₁, a]
    ring
  rw [h_eq]
  have h_sq : (-a) ^ 2 = a ^ 2 := by ring
  rw [h_sq]
  exact htrace

/-- Characteristic-polynomial factorization for elliptic trace and norm parameters. -/
theorem characteristic_poly_roots (q α β t : ℚ)
    (hnorm : α * β = q) :
    1 - (α + β) * t + q * t ^ 2 = (1 - α * t) * (1 - β * t) := by
  rw [← hnorm]
  ring

end InfoGeometry.Canonical.HasseWeilEllipticBounds
