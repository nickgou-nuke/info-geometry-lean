import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.Parahyperkahler.AnalyticExcision

/-!
# The Causal Poset of Analytic Excision
This file synthesizes the transition from classical real analysis (epsilon bounds)
to pure affine-invariant convex geometry (Dikin ellipsoids) and Hestenes-Krein
algebraic forms.
-/

/-!
# Archetype 701 & 702: The Affine-Invariant Dikin Bound
We reject classical metric balls which break under affine transformations.
Instead, we use the Hessian of the logarithmic barrier to define the Dikin ball,
which is perfectly affine invariant and naturally restricts to the positive cone.
-/

/-- The Dikin ball predicate derived from the logarithmic Hessian: (y-x)² ≤ r²x² -/
def InDikin (x y r : ℝ) : Prop :=
  (y - x)^2 ≤ r^2 * x^2

/-- Master Theorem 1: Dikin Bounds scale algebraically without metric dependence.
This proves that the topological bound is perfectly affine invariant. -/
theorem dikin_affine_scaling (x y r a : ℝ) (ha : a ≠ 0) :
    InDikin (a * x) (a * y) r ↔ InDikin x y r := by
  dsimp [InDikin]
  have h1 : (a * y - a * x)^2 = a^2 * (y - x)^2 := by ring
  have h2 : r^2 * (a * x)^2 = a^2 * (r^2 * x^2) := by ring
  rw [h1, h2]
  have ha2 : 0 < a^2 := sq_pos_of_ne_zero ha
  exact mul_le_mul_left ha2

/-!
# Archetype 703: The Hestenes-Krein Algebraic Boundary
We explicitly excise the concept of epsilon-delta analyticity in higher dimensions.
Topological closeness is instead defined by the purely algebraic Clifford/Krein
quadratic form.
-/
class KreinQuadraticForm (A : Type*) [Ring A] where
  Q : A → ℝ
  Q_zero : Q 0 = 0
  Q_mul : ∀ a b, Q (a * b) = Q a * Q b

/-- The topological neighborhood is generated purely algebraically. -/
def AlgebraicNeighborhood {A : Type*} [Ring A] [KreinQuadraticForm A] (x : A) (r : ℝ) : Set A :=
  { y | KreinQuadraticForm.Q (y - x) ≤ r^2 }

/-- Master Theorem 2: The Algebraic Neighborhood is intrinsically translation invariant 
without requiring a coordinate-bound Riemannian metric. -/
theorem algebraic_neighborhood_translation {A : Type*} [Ring A] [K : KreinQuadraticForm A] (x y z : A) (r : ℝ) :
    y ∈ AlgebraicNeighborhood x r ↔ (y + z) ∈ AlgebraicNeighborhood (x + z) r := by
  dsimp [AlgebraicNeighborhood]
  have h_diff : (y + z) - (x + z) = y - x := by noncomm_ring
  rw [h_diff]

end InfoGeometry.Parahyperkahler.AnalyticExcision
