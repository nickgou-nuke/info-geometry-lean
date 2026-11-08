import InfoGeometry.Projective.SelfDualCone
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Cone.Basic

/-!
# Positive Orthant as a Self-Dual Cone

The standard positive orthant in `EuclideanSpace ℝ α` is implemented by
transporting `ProperCone.positive` on the coordinate space `α → ℝ` through
`EuclideanSpace.equiv`.
-/

open scoped BigOperators

noncomputable section

namespace InfoGeometry.Projective

variable {α : Type*} [Fintype α]

/-- Positive orthant in Euclidean coordinates, transported from `α → ℝ`. -/
abbrev positiveOrthantCone : ProperCone ℝ (EuclideanSpace ℝ α) :=
  (ProperCone.positive ℝ (α → ℝ)).comap (EuclideanSpace.equiv α ℝ).toContinuousLinearMap

lemma mem_positiveOrthantCone (x : EuclideanSpace ℝ α) :
    x ∈ positiveOrthantCone (α := α) ↔ ∀ i, 0 ≤ x i := by
  simp [positiveOrthantCone, Pi.le_def]

/-- The standard positive orthant as a self-dual cone in `EuclideanSpace ℝ α`. -/
def positiveOrthant : SelfDualCone (EuclideanSpace ℝ α) where
  cone := positiveOrthantCone (α := α)
  self_dual := by
    ext y
    constructor
    · intro hy
      rw [mem_positiveOrthantCone]
      intro i
      classical
      have hsingle : EuclideanSpace.single i (1 : ℝ) ∈ positiveOrthantCone (α := α) := by
        rw [mem_positiveOrthantCone]
        intro j
        by_cases hji : j = i
        · simp [EuclideanSpace.single_apply, hji]
        · simp [EuclideanSpace.single_apply, hji]
      have h := (ProperCone.mem_innerDual.mp hy) hsingle
      simpa [EuclideanSpace.inner_single_left] using h
    · intro hy
      rw [ProperCone.mem_innerDual]
      intro x hx
      have hx0 : ∀ i, 0 ≤ x i := (mem_positiveOrthantCone (α := α) x).1 hx
      have hxy : inner ℝ x y = ∑ i, x i * y i := by
        simp [PiLp.inner_apply, mul_comm]
      rw [hxy]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx0 i) (hy i))

end InfoGeometry.Projective
