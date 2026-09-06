end CharacterFisherCurvatureShadow

/--
`Cl(4,4)`-style scalar distribution of character degeneracy.

This records the intended split of representation degeneracy between the stress
tensor lane, the central/BPS defect lane, and a residual lane.  It is not a
construction of the concrete `Spin(4,4)` character.
-/
structure Cl44WeylCharacterDistribution where
  stressTensorDegeneracy : ℝ
  centralChargeDegeneracy : ℝ
  residualDegeneracy : ℝ
  totalDegeneracy : ℝ
  totalDegeneracy_eq :
    totalDegeneracy =
      stressTensorDegeneracy + centralChargeDegeneracy + residualDegeneracy

namespace Cl44WeylCharacterDistribution

/-- Total character degeneracy split into stress, central-charge, and residual lanes. -/
theorem total_eq
    (D : Cl44WeylCharacterDistribution) :
    D.totalDegeneracy =
      D.stressTensorDegeneracy + D.centralChargeDegeneracy + D.residualDegeneracy :=
  D.totalDegeneracy_eq

/-- If the residual lane vanishes, degeneracy is exactly stress plus central charge. -/
theorem total_eq_stress_add_central_of_residual_zero
    (D : Cl44WeylCharacterDistribution)
    (h : D.residualDegeneracy = 0) :
    D.totalDegeneracy =
      D.stressTensorDegeneracy + D.centralChargeDegeneracy := by
  rw [D.total_eq, h]
  ring

end Cl44WeylCharacterDistribution

/--
Capstone joining the adapted scalar basis with the Weyl-character partition
interpretation.
-/
structure AdaptedBasisWeylCharacterCapstone (ι : Type*) [Fintype ι] where
  adaptedBasis : InvolutionAdaptedSuperMetriplecticBasis
  characterPacket : WeylCharacterGibbsPacket ι
  superCharacter : SuperWeylCharacterSplit
  witten : WittenIndexCharacterPacket
  fisher : CharacterFisherCurvatureShadow
  cl44Distribution : Cl44WeylCharacterDistribution
  partition_matches_globalShadow :
    characterPacket.partitionFunction = adaptedBasis.globalShadow
  superCharacter_matches_witten :
    witten.split = superCharacter

namespace AdaptedBasisWeylCharacterCapstone

variable {ι : Type*} [Fintype ι]

/-- The Weyl character partition function is the adapted scalar global shadow. -/
theorem partition_eq_globalShadow
    (C : AdaptedBasisWeylCharacterCapstone ι) :
-- [STITCHER: MISSING OVERLAP] --
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
structure WeylCharacterFormulaShadow (ι : Type*) [Fintype ι] where
  characterPacket : WeylCharacterGibbsPacket ι
  numerator : ℝ
  denominator : ℝ
  denominator_ne_zero : denominator ≠ 0
  character_eq_ratio :
    characterPacket.character = numerator / denominator

namespace WeylCharacterFormulaShadow

variable {ι : Type*} [Fintype ι]

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

/--
BPS/Witten specialized character packet.