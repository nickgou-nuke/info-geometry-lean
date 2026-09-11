/-
# SuperBracket.lean

Minimal ℤ₂-graded bracket with ℝ-bilinearity.

Provides the `SuperBracket` typeclass, which is the minimal interface for an
ℝ-linear bracket operation on an `AddCommGroup` with `Module ℝ`.  Higher
structures (`SuperLieRing`, `SuperLieAlgebra`) extend this.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Algebra

/--
`SuperBracket L` is the minimal bracket interface.

It bundles:
- `bracket : L → L → L`            (the bracket operation)
- `add_lie`, `lie_add`             (additivity in each argument)
- `lie_smul`                       (ℝ-linearity in the second argument)

No grading or Jacobi constraints are imposed at this level.
-/
class SuperBracket (L : Type*) extends AddCommGroup L, Module ℝ L where
  bracket : L → L → L
  add_lie : ∀ x y z : L, bracket (x + y) z = bracket x z + bracket y z
  lie_add : ∀ x y z : L, bracket x (y + z) = bracket x y + bracket x z
  lie_smul : ∀ (r : ℝ) (x y : L), bracket x (r • y) = r • bracket x y

/-- Convenience notation `⁅x, y⁆` for the bracket. -/
notation "⁅" x ", " y "⁆" => SuperBracket.bracket x y

namespace SuperBracket

/-- From ℝ-bilinearity we get left ℤ-linearity (the standard `lie_smul` for ℤ). -/
theorem add_lie_left {L : Type*} [SuperBracket L] {x y z : L} :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ :=
  add_lie x y z

/-- From left additivity we get `⁅0, z⁆ = 0`. -/
theorem lie_zero_left {L : Type*} [SuperBracket L] (z : L) : ⁅(0 : L), z⁆ = 0 := by
  have h := add_lie (0 : L) (0 : L) z
  simpa using h

/-- From right additivity we get `⁅x, 0⁆ = 0`. -/
theorem zero_lie {L : Type*} [SuperBracket L] (x : L) : ⁅x, (0 : L)⁆ = 0 := by
  have h := lie_add x (0 : L) (0 : L)
  simpa using h

end SuperBracket
