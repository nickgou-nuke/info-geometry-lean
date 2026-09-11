import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section

namespace InfoGeometry.Analysis

open scoped BigOperators

/-- The trace of a rank-one operator equals the corresponding inner product. -/
theorem trace_rankOne_eq_inner
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H]
    (x y : H) :
    (LinearMap.trace ℝ H) (InnerProductSpace.rankOne ℝ x y) = inner (𝕜 := ℝ) (E := H) y x := by
  simpa using (InnerProductSpace.trace_rankOne (𝕜 := ℝ) (E := H) x y)

/-- The rank-one trace can also be read as the orthonormal-basis sum. -/
theorem trace_rankOne_eq_sum
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H]
    (x y : H) :
    ∑ i, inner (𝕜 := ℝ) (E := H) (stdOrthonormalBasis ℝ H i)
        ((InnerProductSpace.rankOne ℝ x y) (stdOrthonormalBasis ℝ H i)) =
      inner (𝕜 := ℝ) (E := H) y x := by
  calc
    ∑ i, inner (𝕜 := ℝ) (E := H) (stdOrthonormalBasis ℝ H i)
        ((InnerProductSpace.rankOne ℝ x y) (stdOrthonormalBasis ℝ H i))
        =
      (LinearMap.trace ℝ H) (InnerProductSpace.rankOne ℝ x y) := by
        simpa using
          (LinearMap.trace_eq_sum_inner
            (T := (InnerProductSpace.rankOne ℝ x y).toLinearMap)
            (b := stdOrthonormalBasis ℝ H)).symm
    _ = inner (𝕜 := ℝ) (E := H) y x := by
        exact trace_rankOne_eq_inner (H := H) x y

/-- The norm of a rank-one operator is the product of the norms. -/
theorem norm_rankOne_eq
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (x : H₁) (y : H₂) :
    ‖InnerProductSpace.rankOne ℝ x y‖ = ‖x‖ * ‖y‖ := by
  simpa using (InnerProductSpace.norm_rankOne (𝕜 := ℝ) (E := H₁) (F := H₂) x y)

/-- Rank-one operators vanish iff one factor vanishes. -/
theorem rankOne_eq_zero_iff
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (x : H₁) (y : H₂) :
    InnerProductSpace.rankOne ℝ x y = 0 ↔ x = 0 ∨ y = 0 := by
  simpa using (InnerProductSpace.rankOne_eq_zero (𝕜 := ℝ) (x := x) (y := y))

/-- A rank-one operator is nonzero when both factors are nonzero. -/
theorem rankOne_ne_zero_of_ne_zero
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (x : H₁) (y : H₂) (hx : x ≠ 0) (hy : y ≠ 0) :
    InnerProductSpace.rankOne ℝ x y ≠ 0 := by
  intro hzero
  have h := (rankOne_eq_zero_iff (H₁ := H₁) (H₂ := H₂) x y).mp hzero
  exact Or.elim h hx hy

/-- The rank-one operator has zero norm iff one factor vanishes. -/
theorem norm_rankOne_eq_zero_iff
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (x : H₁) (y : H₂) :
    ‖InnerProductSpace.rankOne ℝ x y‖ = 0 ↔ x = 0 ∨ y = 0 := by
  rw [norm_rankOne_eq]
  constructor
  · intro h
    have hxhy : ‖x‖ = 0 ∨ ‖y‖ = 0 := by
      have hmul : ‖x‖ * ‖y‖ = 0 := by simpa [h]
      exact mul_eq_zero.mp hmul
    rcases hxhy with hx | hy
    · left
      exact norm_eq_zero.mp hx
    · right
      exact norm_eq_zero.mp hy
  · intro h
    rcases h with rfl | rfl <;> simp

end InfoGeometry.Analysis
