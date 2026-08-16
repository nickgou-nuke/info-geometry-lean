import InfoGeometry.Canonical.FiniteJaynesFormalism
import InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge
import InfoGeometry.Canonical.JaynesLDDSBridge
import InfoGeometry.Canonical.JaynesInductiveLimitBridge
import InfoGeometry.Canonical.JaynesCategoricalInductionBridge
import InfoGeometry.Canonical.JaynesLDDSCentering
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.MaxEnt.DualBridge
import InfoGeometry.MaxEnt.Finite

/-!
# InfoGeometry.Canonical.JaynesFormalism

Umbrella Jaynes formalism in the repo-native finite/algebraic sense.

This file does not add a new analytic theorem.  It packages the already owned
finite entropy, centered-score, and direct-limit layers under one namespace:

* finite Shannon/cross/KL/LDDS identities;
* finite centered-score and relative-density readback;
* Jaynes-style compatible direct-limit/categorical cone transport;
* canonical Gibbs/MaxEnt and modular-affine facades.

The measure-theoretic and spectral completions remain separate owners.
-/

namespace JaynesFormalism

open Finset
open InfoGeometry.Canonical.AFRecursiveLimitBridge
open InfoGeometry.Canonical.JaynesCategoricalInductionBridge
open InfoGeometry.Canonical.JaynesLDDSCentering
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps
open InfoGeometry.Canonical.FiniteJaynesFormalism
open InfoGeometry.MaxEnt.Finite
open JaynesRNMaxEnt
open InfoGeometry.MaxEnt

export InfoGeometry.MaxEnt (
  entropy
  partition
  logPartition
  gibbs
  gibbsExpectation
  partition_pos
  partition_ne_zero
  gibbs_pos
  gibbs_nonneg
  gibbs_sum_one
  gibbs_eq_exp_sub_logPartition
  gibbsMaxEntProblemOfExpectation
)

export JaynesRNMaxEnt (
  MomentFamily
  Satisfies
  SatisfiesIntegrable
  FeasibleSet
  FeasibleSetIntegrable
  objectiveKL
  potential
  partitionFunction
  PartitionIntegrable
  gibbsMeasure
  gibbs
  gibbs_minimizes_kl
  GibbsMinimizesKL
)

export InfoGeometry.Canonical.JaynesRNMaxEnt (
  scalarModularPotential_exp_potential_div_partition
  neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition
  potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition
)

export InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge (
  FiniteProfile
  FiniteReferenceState
  FiniteJaynesPair
  relativeDensity
  centeredRelativeDensity
  centeredRelativeDensity_self
  relativeDensity_eq_one_add_centered
  ref_weighted_centeredRelativeDensity_eq_mass_sub
  ref_weighted_centeredRelativeDensity_eq_zero_of_equal_mass
)

export InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps (
  IsPositive
  IsNormalized
  observationMass
  referenceMass
  centeredScore
  densityRatio
  relativeCenteredScore
  centeredScore_ref_zero
  centeredScore_eq_sub
  sum_centeredScore_eq_mass_sub
  sum_centeredScore_eq_zero_of_equal_mass
  referenceMass_eq_one_of_normalized
  weight_ne_zero_of_positive
  weight_mul_relativeCenteredScore_eq_centeredScore
  relativeCenteredScore_eq_centeredScore_div
  weight_mul_relativeCenteredScore_eq_centeredScore_of_positive
  toFiniteLDDSDatum
  ldds_centeredScore_eq_relativeCenteredScore
  ldds_weightedCenteredScore_eq
)

export InfoGeometry.Canonical.FiniteJaynesFormalism (
  finiteShannonEntropy
  finiteCrossEntropy
  finiteKLDivergence
  finiteLDDSEntropy
  pointwise_kl_eq_cross_sub_entropy
  finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
  finiteLDDSEntropy_eq_entropy_sub_cross_correction
  finiteExpectation
  finitePartition
  finiteJaynesDual
  finiteGibbsProfile
  finitePartition_summand_pos
  finitePartition_pos_of_atom
  finiteGibbsProfile_mul_partition
  finiteGibbsProfile_pos
)

export InfoGeometry.Canonical.JaynesLDDSBridge (
  JaynesLDDSPacket
)

export InfoGeometry.Canonical.JaynesInductiveLimitBridge (
  JaynesInductivePacket
)

variable {ι : Type*} [Fintype ι]

/-- Jaynes finite entropy decomposes into Shannon entropy plus KL divergence. -/
theorem finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (hobs : ∀ i : ι, 0 < obs i) (href : IsPositive R) :
    finiteCrossEntropy R obs = finiteShannonEntropy obs + finiteKLDivergence R obs :=
  InfoGeometry.Canonical.FiniteJaynesFormalism.finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
    (R := R) (obs := obs) hobs href

/-- Finite LDDS entropy is Shannon entropy corrected by the reference cross term. -/
theorem finiteLDDSEntropy_eq_entropy_sub_cross_correction
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι)
    (hobs : ∀ i : ι, 0 < obs i) (href : IsPositive R) :
    finiteLDDSEntropy R obs = finiteShannonEntropy obs - finiteCrossEntropy R obs :=
  InfoGeometry.Canonical.FiniteJaynesFormalism.finiteLDDSEntropy_eq_entropy_sub_cross_correction
    (R := R) (obs := obs) hobs href

/-- Finite Gibbs partition positivity from an explicitly supplied atom. -/
theorem finitePartition_pos_of_atom
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ)
    (href : IsPositive R) (i0 : ι) :
    0 < finitePartition R observable lam :=
  InfoGeometry.Canonical.FiniteJaynesFormalism.finitePartition_pos_of_atom
    (R := R) (observable := observable) (lam := lam) href i0

/-- Finite Gibbs profile is positive when the partition is positive. -/
theorem finiteGibbsProfile_pos
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) {i : ι}
    (href : IsPositive R) (hZ : 0 < finitePartition R observable lam) :
    0 < finiteGibbsProfile R observable lam i :=
  InfoGeometry.Canonical.FiniteJaynesFormalism.finiteGibbsProfile_pos
    (R := R) (observable := observable) (lam := lam) (i := i) href hZ

/-- Finite Gibbs profile clears the partition denominator. -/
theorem finiteGibbsProfile_mul_partition
    (R : FiniteReferenceState ι) (observable : ι → ℝ) (lam : ℝ) {i : ι}
    (hZ : finitePartition R observable lam ≠ 0) :
    finiteGibbsProfile R observable lam i * finitePartition R observable lam =
      R i * Real.exp (-lam * observable i) :=
  InfoGeometry.Canonical.FiniteJaynesFormalism.finiteGibbsProfile_mul_partition
    (R := R) (observable := observable) (lam := lam) (i := i) hZ

/-- Finite Gibbs probabilities sum to one in the one-moment Jaynes model. -/
theorem gibbs_sum_one
    {n : ℕ} [NeZero n] (f : Fin n → ℝ) (lam : ℝ) :
    ∑ i, InfoGeometry.MaxEnt.gibbs f lam i = 1 :=
  InfoGeometry.MaxEnt.gibbs_sum_one f lam

/-- Jaynes MaxEnt feasibility of the Gibbs family is exactly the moment-matching condition. -/
theorem gibbs_mem_maxEntConstraint_iff
    {n : ℕ} [NeZero n] (f : Fin n → ℝ) (E lam : ℝ) :
    InfoGeometry.MaxEnt.gibbs f lam ∈ InfoGeometry.MaxEnt.MaxEntConstraint (n := n) f E ↔
      InfoGeometry.MaxEnt.gibbsExpectation f lam = E :=
  InfoGeometry.MaxEnt.gibbs_mem_maxEntConstraint_iff f E lam

/-- Jaynes entropy bound on the one-moment constraint set. -/
theorem gibbs_maximizes_entropy_on_constraint
    {n : ℕ} [NeZero n] (f : Fin n → ℝ) (E lam : ℝ)
    (hE : InfoGeometry.MaxEnt.gibbsExpectation f lam = E) :
    ∀ q, q ∈ InfoGeometry.MaxEnt.MaxEntConstraint (n := n) f E →
      InfoGeometry.MaxEnt.entropy q 1 ≤ InfoGeometry.MaxEnt.entropy (InfoGeometry.MaxEnt.gibbs f lam) 1 :=
  InfoGeometry.MaxEnt.gibbs_maximizes_entropy_on_constraint (n := n) f E lam hE

end JaynesFormalism
