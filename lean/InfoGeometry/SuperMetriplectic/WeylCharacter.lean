import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

/-!
# InfoGeometry.SuperMetriplectic.WeylCharacter
-/



namespace InfoGeometry.SuperMetriplectic

variable {ι : Type*} [Fintype ι]

/-- The character is the finite degeneracy-weighted Gibbs sum. -/
theorem character_eq_weighted_sum
    (character : ℝ)
    (degeneracy gibbsFactor : ι → ℝ)
    (h : character = ∑ i, degeneracy i * gibbsFactor i) :
    character = ∑ i, degeneracy i * gibbsFactor i := h

/-- The partition function is the Weyl character readout in this packet. -/
theorem partitionFunction_eq
    (partitionFunction character : ℝ)
    (h : partitionFunction = character) :
    partitionFunction = character := h

/-- Partition function written directly as the character/Gibbs sum. -/
theorem partitionFunction_eq_weighted_sum
    (partitionFunction character : ℝ)
    (degeneracy gibbsFactor : ι → ℝ)
    (h1 : partitionFunction = character)
    (h2 : character = ∑ i, degeneracy i * gibbsFactor i) :
    partitionFunction = ∑ i, degeneracy i * gibbsFactor i := by
  rw [h1, h2]

/-- The stored Weyl character formula is the advertised ratio. -/
theorem character_ratio
    (character numerator denominator : ℝ)
    (h : character = numerator / denominator) :
    character = numerator / denominator := h

/-- Multiplying the stored ratio recovers the numerator. -/
theorem character_mul_denominator_eq_numerator
    (character numerator denominator : ℝ)
    (h1 : character = numerator / denominator)
    (h2 : denominator ≠ 0) :
    character * denominator = numerator := by
  rw [h1]
  exact div_mul_cancel₀ _ h2

/-- Ordinary character equals the even-plus-odd sum. -/
theorem ordinary_eq
    (ordinaryCharacter bosonicContribution fermionicContribution : ℝ)
    (h : ordinaryCharacter = bosonicContribution + fermionicContribution) :
    ordinaryCharacter = bosonicContribution + fermionicContribution := h

/-- Supercharacter equals the even-minus-odd signed sum. -/
theorem super_eq
    (superCharacter bosonicContribution fermionicContribution : ℝ)
    (h : superCharacter = bosonicContribution - fermionicContribution) :
    superCharacter = bosonicContribution - fermionicContribution := h

/-- The supercharacter differs from the ordinary character by twice the odd channel. -/
theorem super_eq_ordinary_minus_two_fermionic
    (superCharacter ordinaryCharacter bosonicContribution fermionicContribution : ℝ)
    (h1 : superCharacter = bosonicContribution - fermionicContribution)
    (h2 : ordinaryCharacter = bosonicContribution + fermionicContribution) :
    superCharacter = ordinaryCharacter - 2 * fermionicContribution := by
  rw [h1, h2]
  ring

end InfoGeometry.SuperMetriplectic
