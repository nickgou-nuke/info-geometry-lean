import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.BohmMadelungOperatorialBridge
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Canonical.IBFrozenModularBridge
import InfoGeometry.Canonical.LogDet
import InfoGeometry.Canonical.ProjectiveStateCore
import InfoGeometry.Canonical.RelativeGeneratorCore
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.Canonical.ThermoFromLogDet
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Volume.LogPotential

/-!
# InfoGeometry.Canonical.RedLine

EN: Canonical bridge surface for the Red Line corridor:
log-volume deformation -> convex/barrier potential -> Burg/Bregman energy ->
partition/log-sum-exp -> free energy, with RN/Jaynes and modular lifts.

BG: Канонична мостова повърхност за коридора на Red Line:
деформация на лог-обем -> бариерен/изпъкнал потенциал -> Burg/Bregman енергия ->
partition/log-sum-exp -> свободна енергия с RN/Jaynes и модуларни повдигания.

Redline: This file is the curated owner-facing export spine for the local
count/projective/modular corridor.

Mathlib: Upstream mathlib provides the assembler substrate for many imported
owners and bridge proofs; this file keeps the repo-native semantic surface.

Comparison: Bilingual consistency is closed by explicit bridge exports from the
imported modules (repo-native statements and mathlib-native realizations are
not treated as interchangeable without named bridge theorems).

Upstairs: Ambient linear/Krein/projective carrier structure remains in the
imported owner modules; this export surface does not claim additional descent.

References:
- Mathlib projectivization and measure/RN APIs used in imported owners.
- `docs/projective_mathlib_canonicalization_plan.md` for owner/translator law.
-/

namespace InfoGeometry.Canonical.RedLine


export InfoGeometry.Canonical.LogDet (
  logDetBarrier
  logDetBregman
)

export InfoGeometry.Volume.LogPotential (
  LogAbsVolume
  logAbsVolume_add
)

export InfoGeometry.Canonical.ThermoFromLogDet (
  energyFromLogDet
  partitionFromLogDet
  freeEnergyFromLogDet
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
)

export InfoGeometry.Canonical.LogSumExp (
  logSumExpPartition
  logSumExp
  logSumExpScaledPartition
  logSumExpScaled
  logSumExp_eq_log_partition
)

export InfoGeometry.Canonical.JaynesRNMaxEnt (
  MomentFamily
  objectiveKL
  potential
  partitionFunction
  gibbsMeasure
  rnDeriv_gibbsMeasure_eq
  rnDeriv_gibbsMeasure_toReal_eq
  GibbsMinimizesKL
)

export InfoGeometry.Canonical.JaynesRNMaxEnt (
  partitionFunction_pos
  scalarModularPotential_exp_potential_div_partition
  neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition
  potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition
)

export InfoGeometry.Canonical.IB (
  ibBlahutArimotoStepFrozen_log_ratio_eq_neg_betaKL_sub_logPartitionFrozen
  ibBlahutArimotoStepFrozen_scalarModularPotential_eq_betaKL_add_logPartitionFrozen
  ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL
)

export InfoGeometry.Canonical.MoE (
  kahlerPotentialRN
  kahlerPotentialRN_eq_neg_logJacobian
  relativeVolumeChangeRN
  relativeVolumeChangeRN_eq_exp_logJacobian
  kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
)

export InfoGeometry.Canonical.KMSSinkhornBridge (
  ibRNPotential_eq_scalarModularPotential_relativeVolumeChange
  jacobianRelativeVolume
  jacobianLogPotential
  exp_neg_jacobianLogPotential_eq_jacobianRelativeVolume
  jacobianLogPotential_eq_scalarModularPotential
)

export InfoGeometry.Canonical.RicciMongeAmpere (
  metricLogDet
  mongeAmpereDensity
  mongeAmpereDensity_eq_exp_metricLogDet
  scalarModularPotential_mongeAmpereDensity_eq_neg_metricLogDet
)

export InfoGeometry.Canonical.ProjectiveStateCore (
  UState
  NonzeroUState
  SameRay
  sameRaySetoid
  ProjectiveState
  logPotential
  AEAddConst
  PotentialClass
  logPotentialClass
  self_eq_mass_smul_normalize
  normalize
  logGenerator
  logGeneratorClass
  normalizedSlice
  probMeasureToUState
  probMeasureToNonzero
  probMeasureToProjectiveState
  normalize_probMeasureToProjectiveState
  pmfToProbMeasure
  pmfToProjectiveState
  normalize_pmfToProjectiveState
  probMeasureToPMF
  probMeasureToPMF_apply
  probMeasureToPMF_pmfToProbMeasure
  pmfToProbMeasure_probMeasureToPMF
  logPotential_pmf_eq_log_rnDeriv
  logPotential_pmf_self_ae
)

export InfoGeometry.Canonical.RelativeGeneratorCore (
  logPotential_smul_left_ae
  logPotential_smul_right_ae
  logGenerator_self
  logGeneratorClass_invariant
)

export InfoGeometry.Canonical.PositiveRayCore (
  PositiveRay
  PositiveOrthantRaySpace
  toConeInteriorStateSpace
  ofConeInteriorStateSpace
  gaugeSection
  Z_gaugeSection
  logDensity
  modularPotential
  gaugeSection_eq_exp_logDensity
  gaugeSection_eq_exp_neg_modularPotential
)

export InfoGeometry.Canonical.RelativePotentialCore (
  representativeRelativeDensity
  representativeRelativeLogDensity
  representativeModularPotential
  representativeRelativeLogDensity_eq_log_sub_log
  representativeRelativeDensity_eq_exp_representativeRelativeLogDensity
  representativeModularPotential_eq_neg_representativeRelativeLogDensity
  representativeRelativeLogDensity_scale_left
  representativeRelativeLogDensity_scale_right
  representativeRelativeLogDensity_scale_scale
  representativeModularPotential_scale_left
  representativeModularPotential_scale_right
  relativeDensity
  relativeLogDensity
  relativeModularPotential
  relativeInformationEnergy
  relativeInformationNorm
  relativeLogDensity_eq_logDensity_sub_logDensity
  relativeDensity_eq_exp_relativeLogDensity
  relativeModularPotential_eq_neg_relativeLogDensity
  relativeModularPotential_eq_logDensity_base_sub_logDensity
  gaugeSection_eq_relativeDensity_mul_gaugeSection
  relativeDensity_self
  relativeLogDensity_self
  relativeModularPotential_self
  relativeInformationEnergy_self
  relativeInformationNorm_self
  relativeInformationEnergy_nonneg
  relativeInformationNorm_nonneg
)

export InfoGeometry.Canonical.RelativePotentialScalarBridge (
  scalarPositiveMeasure
  scalarLogDensity
  scalarModularPotential
  scalarLogDensity_eq_log
  scalarModularPotential_eq_neg_log
  exp_neg_scalarModularPotential_eq
  scalarModularPotential_weylRescale_eq_sub_log
)

export InfoGeometry.Canonical.RelativePotentialDiscreteBridge (
  gaugeSectionFinProb
  toProjectiveState
  gaugeSectionFinProb_absolutelyContinuous
  projectiveLogGenerator_eq_relativeModularPotential_ae
  projectiveLogGenerator_eq_relativeModularPotential
)

export InfoGeometry.Canonical.RelativePotentialCountBridge (
  RelativeCounts
  relativeCountDensity
  relativeCountLogDensity
  relativeLogDensityMean
  relativeModularHamiltonian
  relativeTomitaTakesakiOp
  relativeTomitaTakesakiOp_apply
  positiveMeasureOfCounts
  countMass
  countRay
  gaugeSection_countRay_apply
  gaugeSectionFinProb_countRay_apply_toReal
  relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity
  relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift
  relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_sub_massShift
  projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay
  projectiveLogGenerator_countRay_eq_neg_relativeCountLogDensity_sub_massShift
  projectiveLogGenerator_countRay_eq_projectiveCountHamiltonianProfile
)

export InfoGeometry.Canonical.TomitaTakesaki (
  DiagonalPositiveTimeVector
  PositiveTimeVector
  modularConjugationJ
  modularSignEpsilon
  modularComplexI
  modularSignAdditiveModularFlow
  modularAtomRepresentation
  tomitaRepresentation
)

export InfoGeometry.Krein (
  modular_j
  spectral_epsilon
  complex_i
)

export InfoGeometry.Canonical.BohmMadelungOperatorialBridge (
  polarizedDoubledAmplitude_phaseOrbit_eq_dilationOrbit
  stateGeneratorField_phaseReadout_eq_metric_comp_complex_i
  stateGeneratorField_phaseReadout_eq_metric_comp_K
  stateGeneratorField_inducedDerivation_eq_gauge_add_source
  constantStateGeneratorField_stateInducedDerivation_eq_phaseLinear_add_phaseAntilinear_transport
  constantStateGeneratorField_stateQGTReadout_pair_eq_phaseLinearAntilinear_transport_pair
  potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair
  potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_iff_isPotentialKillingOperator
  potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator
)


end InfoGeometry.Canonical.RedLine
