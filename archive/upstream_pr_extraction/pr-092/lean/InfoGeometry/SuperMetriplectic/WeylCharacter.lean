import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

/-!
# InfoGeometry.SuperMetriplectic.WeylCharacter
-/



namespace InfoGeometry.SuperMetriplectic

variable {ι : Type*} [Fintype ι]

/-- Partition function written directly as the character/Gibbs sum. -/
theorem partitionFunction_eq_weighted_sum
    (partitionFunction character : ℝ)
    (degeneracy gibbsFactor : ι → ℝ)
    (h1 : partitionFunction = character)
    (h2 : character = ∑ i, degeneracy i * gibbsFactor i) :
    partitionFunction = ∑ i, degeneracy i * gibbsFactor i := by
  rw [h1, h2]

/-- Multiplying the stored ratio recovers the numerator. -/
theorem character_mul_denominator_eq_numerator
    (character numerator denominator : ℝ)
    (h1 : character = numerator / denominator)
    (h2 : denominator ≠ 0) :
    character * denominator = numerator := by
  rw [h1]
  exact div_mul_cancel₀ _ h2

/-- The supercharacter differs from the ordinary character by twice the odd channel. -/
theorem super_eq_ordinary_minus_two_fermionic
    (superCharacter ordinaryCharacter bosonicContribution fermionicContribution : ℝ)
    (h1 : superCharacter = bosonicContribution - fermionicContribution)
    (h2 : ordinaryCharacter = bosonicContribution + fermionicContribution) :
    superCharacter = ordinaryCharacter - 2 * fermionicContribution := by
  rw [h1, h2]
  ring

end InfoGeometry.SuperMetriplectic
