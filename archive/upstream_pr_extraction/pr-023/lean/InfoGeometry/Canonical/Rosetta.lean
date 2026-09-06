import InfoGeometry.Jordan.LogDet
import InfoGeometry.Canonical.RedLine
import InfoGeometry.Canonical.CayleyBregmanBridge
import InfoGeometry.Canonical.Attention
import InfoGeometry.Canonical.AttentionEuclidean
import InfoGeometry.Canonical.AttentionSplit
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.FormalScaffold
import InfoGeometry.Canonical.GaugeUnified
import InfoGeometry.Canonical.SuperInference
import InfoGeometry.Canonical.ChiralCliffordBridge
import InfoGeometry.Canonical.CliffordBridge
import InfoGeometry.Canonical.AnomalyInflow
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.ChiralGravity
import InfoGeometry.Canonical.ChiralTorsionRelativeVolume
import InfoGeometry.Canonical.ChiralTorsionGeneralizedKL
import InfoGeometry.Canonical.ChiralTorsionTwistor
import InfoGeometry.Canonical.ChiralTorsionState
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.WeylAnomalySource
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Canonical.WilsonLoop
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Experimental.ModularSpinorBridge
import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Canonical.TwistorOperatorialIncidence
import InfoGeometry.Canonical.BerryConnection
import InfoGeometry.Canonical.BerryPhase
import InfoGeometry.Canonical.Singular
import InfoGeometry.Canonical.RosettaSourceBridge
import InfoGeometry.Canonical.RosettaScaleTransport
import InfoGeometry.Quantum.ModularAnomaly
import InfoGeometry.KK.KasparovCycle

/-!
# Research.Rosetta

Consolidated research-facing façade for the verified correspondences:

- log-det / determinant barrier layer
- thermodynamic (Gibbs) normalization layer
- Bregman/Cayley transport layer
- attention specializations (Euclidean / Lorentzian)

This file is intentionally a façade. It re-exports and names the bridges;
it does not assert new global identifications without explicit hypotheses.
-/

namespace InfoGeometry.Canonical.Rosetta

-- Re-export stable entry points here as they mature.
-- Keep theorem statements assumption-driven (compatibility witnesses explicit).

export InfoGeometry.Canonical.GrandUnification (
  JordanKKTData
  IsJordanKKTGeometry
)

export InfoGeometry.Canonical.Cayley (
  CayleyBridge
  CayleyEquivalence
  CayleyCompatibleDualFlat
  CayleyDualFlatCompatibility
  cayleyPythagoreanInvariance
  cayleyIdentityBridge
  cayleyIdentityCompatibleGeometry
)

export InfoGeometry.Canonical.Attention (
  attentionWeights_sum_one
  euclideanAttentionWeights_sum_one
  lorentzianAttentionWeights_sum_one
  Vec
  Head
)

export InfoGeometry.Canonical.Gauge (
  Signature
  act_preserves_bilinear
)

export InfoGeometry.Canonical.ConformalUnification.ConformalInference (
  P
  K
  D
  specialConformal_eq_modularInversion_translation
  translation_eq_modularInversion_specialConformal
  spectralChiralProjector
  metricChiralProjector
  chiralAnomaly
  chiralAnomalyOperator
  chiralScale
  chiralScale_eq_projectorObstruction_norm
  chiral_commutation_link
  chiralAnomalyOperator_eq_zero_iff_projectors_commute
  projectors_commute_of_chiralAnomaly_eq_zero
  chiralAnomaly_eq_zero_of_projectors_commute
  chiralScale_eq_zero_of_projectors_commute
  chiralScale_ne_zero_of_projectors_not_commute
  chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
  projectors_commute_of_chiralScale_eq_zero
  projectors_commute_of_kahlerLogDet_unitRelativeVolume
  anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
  projectors_commute_of_kahlerLogDet_normalized_fixedpoint
  einsteinEquation_of_projectorObstruction_source
  IsNormalInference
  IsChiralInference
)

export InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra (
  SatisfiesPWeight
  SatisfiesKWeight
  SatisfiesMasterRelation
  SatisfiesFlatWeights
  GeneratorCartanDecomposition
  generatorCartanDecomposition_iff
  generatorCartanDecomposition_of_parts
  GradingInvolutive
  cartanInvolution
  IsVolumePreservingPart
  IsWeylDilationPart
  M_in_volumePreserving_of_cartan
  D_in_weylDilation_of_cartan
  cartan_generator_split
  cartanInvolution_involutive_of_gradingInvolutive
  cartanInvolution_eq_self_of_volumePreserving_of_gradingInvolutive
  cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive
  volumePreserving_of_cartanInvolution_eq_self_of_gradingInvolutive
  weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive
  cartanInvolution_eq_self_iff_volumePreserving_of_gradingInvolutive
  cartanInvolution_eq_neg_self_iff_weylDilation_of_gradingInvolutive
  commutator
  commutator_volumePreserving_volumePreserving
  commutator_volumePreserving_weylDilation
  commutator_weylDilation_weylDilation
  scale_anomaly_obstructs_weyl_flatness
)

export InfoGeometry.Canonical (
  WeylGaugeField
  WeylGaugeParameter
  WeylFieldStrength
  WeylDifferentialOperator
  WeylTrajectory
  WeylLineIntegrator
  WeylHolonomyMap
  ScaleEquivariantFlow
)

export InfoGeometry.Canonical.WeylGaugeField (
  along
  respond
  transform
  transformByPotential
  covariantDerivative
  transformSection
  fieldStrength
  IsFlat
  IsGaugeInvariant
  respond_transform_eq_of_isGaugeInvariant
  fieldStrength_transformByPotential_eq
  covariantDerivative_transformSection_eq
  connectionAlong
  generatedAlong
  responseAlong
  curvatureAlong
  covariantSectionAlong
  curvatureAlong_transformByPotential_eq
  covariantSectionAlong_transform_eq
  covariantGeneratedFlow
  respondCovariantFlow
  respondCovariantFlow_transform_eq
)

export InfoGeometry.Canonical.WeylTrajectory (
  along
)

export InfoGeometry.Canonical.ScaleEquivariantFlow (
  transportObservable
  IsCocycle
  transportObservable_isCocycle
)

export InfoGeometry.Canonical.WeylLineIntegrator (
  finiteSumIntegrator
  finiteSumIntegrator_integrateCurvature_eq_zero_of_flat
  integrateConnection
  integrateCurvature
  integrateCurvature_transformByPotential_eq
  holonomy
  gaugeCompensatedHolonomy
  gaugeCompensatedHolonomy_eq_base_of_boundary_law
)

export InfoGeometry.Canonical.WeylTransportBridge (
  FlatCurvatureChiralScaleBridge
  holonomy_eq_chiralScale_of_flat
  finiteSumFlatCurvatureChiralScaleBridge
  finiteSum_holonomy_eq_chiralScale_of_flat
)

export InfoGeometry.Canonical.SuperInference (
  SuperState
  SuperBeliefState
  superCharge
  susyCharge
  superHamiltonian
  susyHamiltonian
  superCharge_boson_eq_zero
  superCharge_fermion_eq_dualMap
  susyHamiltonian_eq_self
)

export InfoGeometry.Experimental.ModularSpinorBridge (
  MajoranaFrame
  canonicalMajoranaFrame
  spinorBilinear
  ModularBerryBridge
  SpinorInnovationBridge
  spinorBilinear_eq_berryPhase
  spinorBilinear_eq_klDivergence
)

export InfoGeometry.Canonical.ChiralCliffordBridge (
  chiralGrading
  generalizedChiralPlus
  generalizedChiralMinus
  chiralProjectorPlus
  chiralProjectorMinus
  IsCompactBeliefUpdate
  IsNonCompactBeliefUpdate
  anomaly_as_structure_constant
  cartan_collapse_of_normal
)

export InfoGeometry.Canonical.CliffordBridge (
  q_agrees_with_Gauge_quad
  B_agrees_with_Gauge_bilinear
)

export InfoGeometry.Canonical.ChiralTorsionBridge (
  boltzmannRelativeVolumeEntropy
  boltzmannRelativeVolumeEntropy_eq_divergence
  gibbsSmoothingOnGeneralizedKL
  gibbsSmoothingOnGeneralizedKL_pos
  IsVacuumApexNull
  vacuumApexTwistor
  ChiralTorsionChentsovGibbsState
  chentsov_and_gibbs_of_state
  torsion_nonzero_of_chiral
)

export InfoGeometry.Canonical.AnomalyInflow (
  variationChernSimons
  bulkChernSimonsVariation
  boundaryAnomaly
  boundaryAnomalyDensity
  AnomalyInflowClosure
  anomalyInflowClosure
  anomaly_inflow_cancellation
)

export InfoGeometry.Canonical.BerryPhase (
  berryConnection
  informationBerryPhase
  informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex
  informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank
  informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero
  berry_phase_vanishes_for_normal
)

export InfoGeometry.Canonical.ChiralEinsteinBridge (
  anomalyStressEnergyAt
  anomalyStressEnergyModelAt
  einsteinEquation_of_anomaly_source
  exists_einsteinEquation_of_bistochastic_routingAnomaly
  SatisfiesAnomalyDrivenKaehlerRicciFlow
  SatisfiesAnomalyDrivenScalarRicciFlow
  anomalyDriven_fixedpoint_tracks_source
  anomalyDrivenScalarRicci_fixedpoint_tracks_source
  inverseEpsilonSource
  anomalyDriven_fixedpoint_eq_inverseEpsilon
)

export InfoGeometry.Canonical.ChiralGravity (
  anomalyEinsteinResidualAt
  AnomalyCurvatureForcingStateAt
  anomalyEinsteinResidual_eq_kappa_mul_metric
  anomaly_nonzero_forces_curved_plus_component
  anomaly_nonzero_excludes_vacuum
  routingAnomaly_nonzero_forces_curved_plus_component
)

export InfoGeometry.Canonical.BogoliubovFockSuper (
  BogoliubovMixingParams
  FockEndomorphism
  bogoliubovAnnihilation
  bogoliubovCreation
  bogoliubovNumberOperator
  grandCanonicalFockGenerator
  grandCanonicalFockEulerStep
  SuperParity
  paritySign
  fockSuperBracket
  fockCommutator
  fockAnticommutator
  anticommutator_annihilation_self
  anticommutator_creation_self
  anticommutator_annihilation_creation
  commutator_annihilation_self
  commutator_creation_self
  commutator_annihilation_creation
  anticommutator_symm
  fockAnticommutator_symm
  commutator_swap
  fockCommutator_swap
  superBracket_bogoliubov_covariance
  anticommutator_bogoliubov_projector_model
  commutator_bogoliubov_projector_model
  einsteinInducedChemicalPotential
  einsteinFockDeformationOperator
  grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
)

export InfoGeometry.Canonical.TomitaTakesaki (
  modularCPTSupercharge
  modularComplexI_eq_dilationOperator
  modularCPTSupercharge_Q_eq_dilationOperator
)

export InfoGeometry.Canonical (
  IsMoorePenroseInverse
  IsDrazinInverse
  EinsteinAnomaly
  exists_regularization_pair_of_isUnit
  EinsteinAnomaly_eq_zero_of_regularization_pair
)

export InfoGeometry.Twistor.Incidence (
  Twistor
  Incident
  pointAction
  twistorMap
  incident_points_null_separated
)

export InfoGeometry.Canonical.RedLine (
  logDetBarrier
  logDetBregman
  energyFromLogDet
  partitionFromLogDet
  freeEnergyFromLogDet
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
  logSumExpPartition
  logSumExp
  logSumExpScaledPartition
  logSumExpScaled
  MomentFamily
  objectiveKL
  partitionFunction
  gibbsMeasure
  rnDeriv_gibbsMeasure_eq
  rnDeriv_gibbsMeasure_toReal_eq
  kahlerPotentialRN
  relativeVolumeChangeRN
  relativeModularHamiltonian
  relativeTomitaTakesakiOp
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

export InfoGeometry.Canonical.WilsonLoop (
  DiracField
  diracReg
  wilsonStep
  wilsonPropagatorDiscrete
  wilsonLoopDiscrete
  continuousWilsonLoop
  chiralPathWeight
  chiralPathIntegral
  expectedHolonomy
  BeliefSystem
  gaussianDiracField
  gaussianWilsonLoopDiscrete
  gaussian_holonomy_flat
)

export InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem (
  non_commutative_updates
  InformationLieAlgebra
)

end InfoGeometry.Canonical.Rosetta
