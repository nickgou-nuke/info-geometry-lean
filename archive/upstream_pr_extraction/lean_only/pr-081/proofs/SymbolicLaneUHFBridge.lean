import Mathlib

/-!
# Symbolic Lane to UHF Boundary Bridge

The symbolic occupation marker `eᵢ` is realized as the `i`th coordinate
projection on the diagonal UHF/Cantor boundary:

`eᵢ(b) = 1` if `b i = true`, and `0` otherwise.

Thus the symbolic CAS lane becomes a genuine cylinder observable.  The local
graded lane evaluates pointwise to `1` on the empty bit and `-x` on the
occupied bit; Boolean summation over the bit gives the finite local factor
`1 - x`.
-/

noncomputable section

namespace SymbolicLaneUHFBridge

abbrev CantorBoundary : Type :=
  ℕ → Bool

/-- Boundary coordinate projection, valued as a complex idempotent. -/
def coordinateIdempotent (i : ℕ) (b : CantorBoundary) : ℂ :=
  if b i then 1 else 0

/-- Symbolic local occupation lane. -/
def occupationLane (e x : ℂ) : ℂ :=
  (1 - e) + e * x

/-- Symbolic local parity lane. -/
def parityLane (e : ℂ) : ℂ :=
  1 - 2 * e

/-- Symbolic local graded lane. -/
def gradedLane (e x : ℂ) : ℂ :=
  parityLane e * occupationLane e x

/-- Local graded lane as a UHF diagonal boundary observable. -/
def boundaryGradedLane (i : ℕ) (x : ℂ) : CantorBoundary → ℂ :=
  fun b => gradedLane (coordinateIdempotent i b) x

theorem coordinateIdempotent_sq (i : ℕ) (b : CantorBoundary) :
    coordinateIdempotent i b * coordinateIdempotent i b =
      coordinateIdempotent i b := by
  by_cases h : b i
  · simp [coordinateIdempotent, h]
  · simp [coordinateIdempotent, h]

theorem occupationLane_empty (x : ℂ) :
    occupationLane 0 x = 1 := by
  simp [occupationLane]

theorem occupationLane_occupied (x : ℂ) :
    occupationLane 1 x = x := by
  simp [occupationLane]

theorem parityLane_empty :
    parityLane 0 = 1 := by
  simp [parityLane]

theorem parityLane_occupied :
    parityLane 1 = -1 := by
  norm_num [parityLane]

theorem gradedLane_empty (x : ℂ) :
    gradedLane 0 x = 1 := by
  simp [gradedLane, parityLane, occupationLane]

theorem gradedLane_occupied (x : ℂ) :
    gradedLane 1 x = -x := by
  norm_num [gradedLane, parityLane, occupationLane]

/-- Pointwise selector form of the local UHF graded lane. -/
theorem boundaryGradedLane_apply (i : ℕ) (x : ℂ) (b : CantorBoundary) :
    boundaryGradedLane i x b = if b i then -x else 1 := by
  by_cases h : b i
  · simp [boundaryGradedLane, coordinateIdempotent, h, gradedLane_occupied]
  · simp [boundaryGradedLane, coordinateIdempotent, h, gradedLane_empty]

/-- Boolean trace over one UHF coordinate gives the local graded determinant. -/
theorem local_boolean_trace (x : ℂ) :
    gradedLane 0 x + gradedLane 1 x = 1 - x := by
  simp [gradedLane_empty, gradedLane_occupied]
  ring

/-- Two-coordinate Boolean trace factors. -/
theorem two_coordinate_boolean_trace (x y : ℂ) :
    (gradedLane 0 x * gradedLane 0 y) +
      (gradedLane 0 x * gradedLane 1 y) +
      (gradedLane 1 x * gradedLane 0 y) +
      (gradedLane 1 x * gradedLane 1 y)
      =
    (1 - x) * (1 - y) := by
  simp [gradedLane_empty, gradedLane_occupied]
  ring

/-- Three-coordinate Boolean trace gives the three-prime graded determinant. -/
theorem three_coordinate_boolean_trace (x y z : ℂ) :
    (gradedLane 0 x * gradedLane 0 y * gradedLane 0 z) +
      (gradedLane 0 x * gradedLane 0 y * gradedLane 1 z) +
      (gradedLane 0 x * gradedLane 1 y * gradedLane 0 z) +
      (gradedLane 0 x * gradedLane 1 y * gradedLane 1 z) +
      (gradedLane 1 x * gradedLane 0 y * gradedLane 0 z) +
      (gradedLane 1 x * gradedLane 0 y * gradedLane 1 z) +
      (gradedLane 1 x * gradedLane 1 y * gradedLane 0 z) +
      (gradedLane 1 x * gradedLane 1 y * gradedLane 1 z)
      =
    (1 - x) * (1 - y) * (1 - z) := by
  simp [gradedLane_empty, gradedLane_occupied]
  ring

/--
Consolidated bridge:
symbolic idempotents are UHF boundary coordinates, local graded lanes are
pointwise selectors, and Boolean trace recovers finite graded Euler factors.
-/
theorem symbolic_lane_uhf_bridge_synthesis :
    (∀ i : ℕ, ∀ b : CantorBoundary,
      coordinateIdempotent i b * coordinateIdempotent i b =
        coordinateIdempotent i b) ∧
    (∀ i : ℕ, ∀ x : ℂ, ∀ b : CantorBoundary,
      boundaryGradedLane i x b = if b i then -x else 1) ∧
    (∀ x : ℂ, gradedLane 0 x + gradedLane 1 x = 1 - x) ∧
    (∀ x y : ℂ,
      (gradedLane 0 x * gradedLane 0 y) +
        (gradedLane 0 x * gradedLane 1 y) +
        (gradedLane 1 x * gradedLane 0 y) +
        (gradedLane 1 x * gradedLane 1 y)
        =
      (1 - x) * (1 - y)) ∧
    (∀ x y z : ℂ,
      (gradedLane 0 x * gradedLane 0 y * gradedLane 0 z) +
        (gradedLane 0 x * gradedLane 0 y * gradedLane 1 z) +
        (gradedLane 0 x * gradedLane 1 y * gradedLane 0 z) +
        (gradedLane 0 x * gradedLane 1 y * gradedLane 1 z) +
        (gradedLane 1 x * gradedLane 0 y * gradedLane 0 z) +
        (gradedLane 1 x * gradedLane 0 y * gradedLane 1 z) +
        (gradedLane 1 x * gradedLane 1 y * gradedLane 0 z) +
        (gradedLane 1 x * gradedLane 1 y * gradedLane 1 z)
        =
      (1 - x) * (1 - y) * (1 - z)) := by
  exact ⟨coordinateIdempotent_sq,
    boundaryGradedLane_apply,
    local_boolean_trace,
    two_coordinate_boolean_trace,
    three_coordinate_boolean_trace⟩

end SymbolicLaneUHFBridge

end noncomputable section
