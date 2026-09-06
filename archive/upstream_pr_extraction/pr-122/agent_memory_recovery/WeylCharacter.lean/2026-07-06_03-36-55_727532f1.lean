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