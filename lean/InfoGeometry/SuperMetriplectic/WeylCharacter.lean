import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

/-!
# InfoGeometry.SuperMetriplectic.WeylCharacter
-/

structure WeylCharacterGibbsPacket (ι : Type*) [Fintype ι] where
  weightReadout : ι → ℝ
  degeneracy : ι → ℝ
  gibbsFactor : ι → ℝ
  character : ℝ
  partitionFunction : ℝ
  character_eq_sum :
    character = ∑ i, degeneracy i * gibbsFactor i
  partitionFunction_eq_character :
    partitionFunction = character

namespace WeylCharacterGibbsPacket

variable {ι : Type*} [Fintype ι]

/-- The character is the finite degeneracy-weighted Gibbs sum. -/
theorem character_eq_weighted_sum
    (W : WeylCharacterGibbsPacket ι) :
    W.character = ∑ i, W.degeneracy i * W.gibbsFactor i :=
  W.character_eq_sum

/-- The partition function is the Weyl character readout in this packet. -/
theorem partitionFunction_eq
    (W : WeylCharacterGibbsPacket ι) :
    W.partitionFunction = W.character :=
  W.partitionFunction_eq_character

/-- Partition function written directly as the character/Gibbs sum. -/
theorem partitionFunction_eq_weighted_sum
    (W : WeylCharacterGibbsPacket ι) :
    W.partitionFunction = ∑ i, W.degeneracy i * W.gibbsFactor i := by
  rw [W.partitionFunction_eq, W.character_eq_weighted_sum]

end WeylCharacterGibbsPacket

/--
Conservative symbolic packet for the Weyl character formula.

This records the ratio shape of the Weyl character formula without claiming a
concrete semisimple Lie algebra, root system, or denominator identity owner in
this file.
-/
abbrev WeylCharacterFormulaData (ι : Type*) [Fintype ι] :=
  WeylCharacterGibbsPacket ι × ℝ × ℝ

def WeylCharacterFormulaShadow (ι : Type*) [Fintype ι] :=
  {d : WeylCharacterFormulaData ι //
    d.2.2 ≠ 0 ∧ d.1.character = d.2.1 / d.2.2}

namespace WeylCharacterFormulaShadow

variable {ι : Type*} [Fintype ι]

def characterPacket (W : WeylCharacterFormulaShadow ι) :
    WeylCharacterGibbsPacket ι := W.1.1

def numerator (W : WeylCharacterFormulaShadow ι) : ℝ := W.1.2.1

def denominator (W : WeylCharacterFormulaShadow ι) : ℝ := W.1.2.2

def denominator_ne_zero (W : WeylCharacterFormulaShadow ι) : W.denominator ≠ 0 :=
  W.2.1

def character_eq_ratio (W : WeylCharacterFormulaShadow ι) :
    W.characterPacket.character = W.numerator / W.denominator :=
  W.2.2

def mk (characterPacket : WeylCharacterGibbsPacket ι)
    (numerator denominator : ℝ)
    (denominator_ne_zero : denominator ≠ 0)
    (character_eq_ratio : characterPacket.character = numerator / denominator) :
    WeylCharacterFormulaShadow ι :=
  ⟨(characterPacket, numerator, denominator),
    ⟨denominator_ne_zero, character_eq_ratio⟩⟩

/-- The stored Weyl character formula is the advertised ratio. -/
theorem character_ratio
    (W : WeylCharacterFormulaShadow ι) :
    W.characterPacket.character = W.numerator / W.denominator :=
  W.character_eq_ratio

/-- Multiplying the stored ratio recovers the numerator. -/
theorem character_mul_denominator_eq_numerator
    (W : WeylCharacterFormulaShadow ι) :
    W.characterPacket.character * W.denominator = W.numerator := by
  rw [W.character_ratio]
  exact div_mul_cancel₀ _ W.denominator_ne_zero

end WeylCharacterFormulaShadow

/--
Even/odd character split.

The ordinary character adds bosonic and fermionic contributions.  The
supercharacter subtracts the fermionic contribution, so it is signed in exactly
the same sense as the supertrace Fisher shadow.
-/
structure SuperWeylCharacterSplit where
  bosonicContribution : ℝ
  fermionicContribution : ℝ
  ordinaryCharacter : ℝ
  superCharacter : ℝ
  ordinaryCharacter_eq :
    ordinaryCharacter = bosonicContribution + fermionicContribution
  superCharacter_eq :
    superCharacter = bosonicContribution - fermionicContribution

namespace SuperWeylCharacterSplit

/-- Ordinary character equals the even-plus-odd sum. -/
theorem ordinary_eq (S : SuperWeylCharacterSplit) :
    S.ordinaryCharacter = S.bosonicContribution + S.fermionicContribution :=
  S.ordinaryCharacter_eq

/-- Supercharacter equals the even-minus-odd signed sum. -/
theorem super_eq (S : SuperWeylCharacterSplit) :
    S.superCharacter = S.bosonicContribution - S.fermionicContribution :=
  S.superCharacter_eq

/-- The supercharacter differs from the ordinary character by twice the odd channel. -/
theorem super_eq_ordinary_minus_two_fermionic
    (S : SuperWeylCharacterSplit) :
    S.superCharacter =
      S.ordinaryCharacter - 2 * S.fermionicContribution := by
  rw [S.super_eq, S.ordinary_eq]
  ring

end SuperWeylCharacterSplit
