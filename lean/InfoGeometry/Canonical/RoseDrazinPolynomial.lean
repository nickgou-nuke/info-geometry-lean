import Mathlib

/-!
# Rose Drazin Polynomial

Finite theorem layer extracted from Nicholas J. Rose, "A Note On Computing the
Drazin Inverse" (Linear Algebra and its Applications 15, 1976, 95--98).

Rose shows how to compute the Drazin inverse as a polynomial in `A` using only
the characteristic polynomial.  This file formalizes the theorem-safe algebra
behind Example 1:

`c(λ) = λ²(λ² + 5λ + 1)`.

For the nonsingular block `C`, the equation `C² + 5C + 1 = 0` gives
`C⁻¹ = -C - 5`; for the nilpotent block `N² = 0`, the Drazin inverse kills the
nilpotent lane.  The block pair `(N, C)` is modeled by the product ring.

#### BUCKET 1: CLOSED FINITE THEOREMS
The inverse-power identities for `λ² + 5λ + 1`, and the Drazin equations for
the exact block model of Rose Example 1.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Drazin equations depend only on the explicit premises `N² = 0` and
`C² + 5C + 1 = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
The all-degree characteristic-polynomial algorithm, Jordan decomposition,
minimal-polynomial reduction, and eigenvalue classification are not asserted
in Lean here.
-/

namespace InfoGeometry.Canonical.RoseDrazinPolynomial

noncomputable section

variable {R : Type} [Field R]

/-- Rose Example 1 inverse candidate for the nonsingular block. -/
def roseExampleOneInverseBlock (c : R) : R :=
  -c - 5

/-- From `c² + 5c + 1 = 0`, Rose obtains `c⁻¹ = -c - 5`. -/
theorem roseExampleOne_right_inverse
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    c * roseExampleOneInverseBlock c = 1 := by
  unfold roseExampleOneInverseBlock
  have htail : c ^ 2 + 5 * c = -1 := by
    rw [← sub_eq_zero]
    linear_combination hc
  calc
    c * (-c - 5) = -(c ^ 2 + 5 * c) := by ring
    _ = -(-1) := by rw [htail]
    _ = 1 := by ring

/-- In a field, the same candidate is also a left inverse. -/
theorem roseExampleOne_left_inverse
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    roseExampleOneInverseBlock c * c = 1 := by
  rw [mul_comm]
  exact roseExampleOne_right_inverse c hc

/--
Rose's recursive inverse-power computation in Example 1 reaches
`c³ * (-24c - 115) = 1`.
-/
theorem roseExampleOne_inversePower_three
    (c : R)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    c ^ 3 * (-24 * c - 115) = 1 := by
  have hc2 : c ^ 2 = -5 * c - 1 := by
    rw [← sub_eq_zero]
    linear_combination hc
  have hc3 : c ^ 3 = 24 * c + 5 := by
    calc
      c ^ 3 = c * c ^ 2 := by ring
      _ = c * (-5 * c - 1) := by rw [hc2]
      _ = -5 * c ^ 2 - c := by ring
      _ = -5 * (-5 * c - 1) - c := by rw [hc2]
      _ = 24 * c + 5 := by ring
  calc
    c ^ 3 * (-24 * c - 115) = (24 * c + 5) * (-24 * c - 115) := by rw [hc3]
    _ = -576 * c ^ 2 - 2880 * c - 575 := by ring
    _ = -576 * (-5 * c - 1) - 2880 * c - 575 := by rw [hc2]
    _ = 1 := by ring

/-- Block model for Rose Example 1: nilpotent block and nonsingular block. -/
def roseExampleOneBlock (n c : R) : R × R :=
  (n, c)

/-- Drazin candidate for the Rose Example 1 block model. -/
def roseExampleOneDrazinBlock (c : R) : R × R :=
  (0, roseExampleOneInverseBlock c)

/-- Rose Example 1 satisfies the index-two Drazin equations in the block model. -/
theorem roseExampleOne_drazin_equations
    (n c : R)
    (hn : n ^ 2 = 0)
    (hc : c ^ 2 + 5 * c + 1 = 0) :
    let A := roseExampleOneBlock n c
    let X := roseExampleOneDrazinBlock c
    A * X = X * A ∧ X * A * X = X ∧ A ^ 3 * X = A ^ 2 := by
  intro A X
  constructor
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock,
        roseExampleOneInverseBlock]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock,
        roseExampleOneInverseBlock]
      ring
  constructor
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        roseExampleOneInverseBlock c * c * roseExampleOneInverseBlock c
            = (c * roseExampleOneInverseBlock c) * roseExampleOneInverseBlock c := by ring
        _ = 1 * roseExampleOneInverseBlock c := by rw [roseExampleOne_right_inverse c hc]
        _ = roseExampleOneInverseBlock c := by ring
  · ext
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      rw [hn]
    · simp [A, X, roseExampleOneBlock, roseExampleOneDrazinBlock]
      calc
        c ^ 3 * roseExampleOneInverseBlock c = c ^ 2 * (c * roseExampleOneInverseBlock c) := by ring
        _ = c ^ 2 * 1 := by rw [roseExampleOne_right_inverse c hc]
        _ = c ^ 2 := by ring

end

end InfoGeometry.Canonical.RoseDrazinPolynomial
