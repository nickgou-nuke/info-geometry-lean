import InfoGeometry.SuperMetriplectic.AdaptedBasis

/-!
# Weyl Character as a Gibbs/Souriau Partition Shadow

Conservative finite character packets for the statement that a Weyl character
can be read as a Gibbs partition function:

* weights are finite labels for moment-map readouts;
* degeneracies are scalar body readouts;
* Gibbs factors are supplied as already-computed scalar factors;
* the supercharacter is the signed even-minus-odd specialization;
* the BPS/Witten index is a temperature-invariant specialized supercharacter.

This file does not prove the Weyl character formula or denominator identity for
a concrete root system.  It provides the finite scalar interface into which such
operator/root-system theorems can later be plugged.
-/

namespace InfoGeometry.SuperMetriplectic

open scoped BigOperators

/--
Finite Weyl-character/Gibbs packet.

`gibbsFactor i` is the scalar shadow of `exp(-⟪μᵢ, β⟫)`.  Keeping it as a
field avoids pretending that this layer owns the analytic exponential/root
system construction.
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

The Witten index is represented as a specialized supercharacter with vanishing
temperature derivative.
-/
structure WittenIndexCharacterPacket where
  split : SuperWeylCharacterSplit
  indexValue : ℝ
  temperatureDerivative : ℝ
  indexValue_eq_superCharacter :
    indexValue = split.superCharacter
  temperatureDerivative_eq_zero :
    temperatureDerivative = 0

namespace WittenIndexCharacterPacket

/-- The Witten index is the specialized supercharacter. -/
theorem index_eq_superCharacter
    (W : WittenIndexCharacterPacket) :
    W.indexValue = W.split.superCharacter :=
  W.indexValue_eq_superCharacter

/-- BPS specialization is temperature-invariant in this packet. -/
theorem temperatureDerivative_zero
    (W : WittenIndexCharacterPacket) :
    W.temperatureDerivative = 0 :=
  W.temperatureDerivative_eq_zero

end WittenIndexCharacterPacket

/--
Character-level Fisher/degeneracy response shadow.

The Fisher curvature is recorded as the response of the degeneracy-weighted
character under variation of the thermodynamic vector.  Positivity is supplied
at body level, matching the rest of the super-metriplectic scalar corridor.
-/
structure CharacterFisherCurvatureShadow where
  massieuPotential : ℝ
  fisherCurvature : ℝ
  degeneracyResponse : ℝ
  fisherCurvature_eq_degeneracyResponse :
    fisherCurvature = degeneracyResponse
  fisherCurvature_nonnegative :
    0 ≤ fisherCurvature

namespace CharacterFisherCurvatureShadow

/-- Fisher curvature is the character degeneracy-response readout. -/
theorem fisher_eq_degeneracyResponse
    (F : CharacterFisherCurvatureShadow) :
    F.fisherCurvature = F.degeneracyResponse :=
  F.fisherCurvature_eq_degeneracyResponse

/-- Character Fisher curvature is body-nonnegative in this packet. -/
theorem fisher_nonnegative
    (F : CharacterFisherCurvatureShadow) :
    0 ≤ F.fisherCurvature :=
  F.fisherCurvature_nonnegative

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
    C.characterPacket.partitionFunction = C.adaptedBasis.globalShadow :=
  C.partition_matches_globalShadow

/-- Witten index is the supercharacter after the BPS specialization. -/
theorem witten_index_eq_superCharacter
    (C : AdaptedBasisWeylCharacterCapstone ι) :
    C.witten.indexValue = C.superCharacter.superCharacter := by
  rw [C.witten.index_eq_superCharacter, C.superCharacter_matches_witten]

/-- The Witten-index character is temperature-invariant. -/
theorem witten_temperatureDerivative_zero
    (C : AdaptedBasisWeylCharacterCapstone ι) :
    C.witten.temperatureDerivative = 0 :=
  C.witten.temperatureDerivative_zero

/-- The character Fisher curvature remains body-nonnegative. -/
theorem character_fisher_nonnegative
    (C : AdaptedBasisWeylCharacterCapstone ι) :
    0 ≤ C.fisher.fisherCurvature :=
  C.fisher.fisher_nonnegative

/--
Combined Weyl-character capstone:
partition equals adapted global shadow, BPS index equals supercharacter,
temperature derivative vanishes, Fisher curvature is nonnegative, and the
`Cl(4,4)` degeneracy distribution is exposed.
-/
theorem weyl_character_adapted_basis_capstone
    (C : AdaptedBasisWeylCharacterCapstone ι) :
    C.characterPacket.partitionFunction = C.adaptedBasis.globalShadow
      ∧ C.witten.indexValue = C.superCharacter.superCharacter
      ∧ C.witten.temperatureDerivative = 0
      ∧ 0 ≤ C.fisher.fisherCurvature
      ∧ C.cl44Distribution.totalDegeneracy =
          C.cl44Distribution.stressTensorDegeneracy
            + C.cl44Distribution.centralChargeDegeneracy
            + C.cl44Distribution.residualDegeneracy := by
  exact ⟨C.partition_eq_globalShadow,
    C.witten_index_eq_superCharacter,
    C.witten_temperatureDerivative_zero,
    C.character_fisher_nonnegative,
    C.cl44Distribution.total_eq⟩

end AdaptedBasisWeylCharacterCapstone

end InfoGeometry.SuperMetriplectic
