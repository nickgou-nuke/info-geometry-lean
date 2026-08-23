import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Canonical.BohmMadelungOperatorialBridge
import InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Canonical.JaynesRNMaxEnt
import InfoGeometry.Canonical.JaynesRNModularBridge
import InfoGeometry.Canonical.IBFrozenModularBridge
import InfoGeometry.Jordan.LogDet
import InfoGeometry.MeasureProjective
import InfoGeometry.Measure.Normalized
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.DeRhamModularPotentialBridge
import InfoGeometry.Canonical.DeRhamThermodynamicPotential
import InfoGeometry.Canonical.QuantumAlgebraObservableBase
import InfoGeometry.Canonical.HomogeneousModularFlows
import InfoGeometry.Canonical.MaurerCartanFactorization
import InfoGeometry.Canonical.RelativePotentialDiscreteBridge
import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
import InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus
import InfoGeometry.Canonical.ContinuousDeRhamPotentialBridge
import InfoGeometry.Continuous.DeRhamBridge
import InfoGeometry.Continuous.PositiveOrthant
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.LogSumExp
import InfoGeometry.Thermo.FromLogDet
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

universe u

export InfoGeometry.Analysis.PositiveOrthantSurprisalCalculus (
  coordinateSurprisalPotential
  hasFDerivAt_coordinateSurprisalPotential
  coordinateSurprisalPotential_contDiffOn
  integral_coordinateSurprisalRate_eq_potential_sub
  coordinateSurprisalPotential_difference
  coordinateSurprisalPotential_closed_loop
  coordinateFisherMetric
  coordinateFisherMetric_comm
  coordinateFisherMetric_add_left
  coordinateFisherMetric_add_right
  coordinateFisherMetric_smul_left
  coordinateFisherMetric_smul_right
  coordinateFisherMetric_nonneg
  coordinateFisherMetric_pos_of_coordinate_ne_zero
  coordinateFisherMetric_pos_of_ne_zero
  coordinateFisherMetric_eq_zero_of_zero
)

export InfoGeometry.Canonical.ContinuousDeRhamPotentialBridge (
  trajectoryPotential
  hasDerivAt_trajectoryPotential
  deriv_trajectoryPotential
  trajectoryPotential_difference
  trajectoryPotential_closed_loop
)

export InfoGeometry.Continuous.DeRhamBridge (
  zeroForm
  exactOneForm
  zeroForm_hasFDerivAt
  zeroForm_contDiffOn_positiveOrthant
  exactOneForm_is_derivative
  exactOneForm_path_integral
)

export InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus (
  coordinateCLM
  coordinateCLM_apply
  coordinateLogPotential
  hasFDerivAt_coordinateLogPotential
  differentiableOn_coordinateLogPotential
  coordinateLogPotential_contDiffOn
  integral_coordinateLogRate_eq_potential_sub
)

/-! The native Redline cocycle package.  This is an export-surface theorem:
the relative-potential owner remains the authority for the three component
proofs, while this namespace exposes their joint multiplicative/additive/
exponential statement to downstream Redline developments. -/
theorem log_exponential_duality_cocycle
    {α : Type u} [Fintype α] [Nonempty α]
    (q q0 q1 : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α) (a : α) :
    (InfoGeometry.Canonical.RelativePotentialCore.relativeDensity q q1 a =
      InfoGeometry.Canonical.RelativePotentialCore.relativeDensity q q0 a *
        InfoGeometry.Canonical.RelativePotentialCore.relativeDensity q0 q1 a) ∧
    (InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q q1 a =
      InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q q0 a +
        InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q0 q1 a) ∧
    (InfoGeometry.Canonical.RelativePotentialCore.relativeDensity q q1 a =
      Real.exp (-InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q q1 a)) := by
  exact InfoGeometry.Canonical.RelativePotentialCore.log_exponential_duality_cocycle q q0 q1 a

/-- Native scalar scale/shape calibration for the RedLine potential. -/
theorem redline_neg_log_mass_scale_shape
    {α : Type u} [Fintype α] [Nonempty α]
    (μ : InfoGeometry.PositiveMeasure α ℝ) (a : α) :
    -Real.log (μ a) =
      -Real.log (InfoGeometry.PositiveMeasure.Z (α := α) (R := ℝ) μ) -
        Real.log (InfoGeometry.PositiveMeasure.normalize μ a) := by
  exact InfoGeometry.Canonical.RelativePotentialCore.neg_log_mass_scale_shape_split μ a

/-! The finite de Rham shadow is exported from its dedicated owner.  These
names are discrete exact-form statements on positive rays; they do not claim
the existence of a smooth manifold or a full differential-form library. -/
export InfoGeometry.Canonical.DeRhamModularPotentialBridge (
  StatisticalManifold
  ZeroForm
  OneForm
  scalarPotential_zeroForm
  dZeroForm
  modularPotential_is_exact_oneForm
  dOneForm
  discrete_exterior_derivative_sq_zero
  modularPotential_antisymm
  modularPotential_closed_loop
  path_independence_of_exact_oneForm
  IsClosedOneForm
  IsExactOneForm
  exact_oneForm_is_closed
  exact_oneForm_path_independence
  exact_oneForm_closed_loop
  path_independence_to_exact_oneForm
  exact_oneForm_iff_path_independence
  modularPotential_is_closed_oneForm
  modularPotential_is_exact_oneForm'
  modular_potential_closed_and_exact
  gibbs_distribution_is_exponential_map
  modularHamiltonian
  modular_flow_is_exponential
)

/-! The general exact-form lemmas and their positive-ray specialization are
    both exposed on the canonical RedLine surface. -/
export InfoGeometry.Canonical.DeRhamPotential (
  ZeroForm
  OneForm
  dZeroForm
  dZeroForm_apply
  exact_oneForm_cocycle
  exact_oneForm_antisymm
  exact_oneForm_self
  dZeroForm_linear
  modularZeroForm
  relativeModularPotential_eq_dZeroForm
  modularZeroForm_deriv_independent
  relativeModularPotential_path_independence
)

export InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge (
  madelung_fisher_rao_line_element
  madelung_quantum_potential_linearization
  bohm_potential_eq_surprisal_laplacian_sub_gradientSq
  surprisalBohmReadout
  doubled_surprisal_bohm_common_readout
  doubled_surprisal_bohm_relative_readout
)

export InfoGeometry.Canonical.QuantumAlgebraObservableBase (
  QuantumAlgebraBundleBase
  ExpectationCoordinateData
  PositiveObservableReadout
)

export InfoGeometry.Canonical.QuantumAlgebraObservableBase.ExpectationCoordinateData (
  basePoint
  fiberAt
  transitionPotential
  potentialField
  transitionPotential_self
  transitionPotential_antisymm
  transitionPotential_transitive
  transitionPotential_closed_loop
  transitionPotential_eq_potentialField_difference
  bundlePotentialField_transport
)

export InfoGeometry.Canonical.QuantumAlgebraObservableBase.QuantumAlgebraBundleBase (
  potentialField_transport
)

export InfoGeometry.Canonical.QuantumAlgebraObservableBase.PositiveObservableReadout (
  toExpectationCoordinateData
  toExpectationCoordinateData_coordinate
)

export InfoGeometry.Canonical.HomogeneousModularFlows (
  maurerCartanDerivative
  maurerCartanPath
  maurerCartanPath_eq_logarithmicBridge
  capstone_logarithmicBridge_factors_maurerCartan
  maurerCartanDerivative_mul_eq_add
  maurerCartanUnit_mul_eq_add
)

export InfoGeometry.Canonical.MaurerCartanFactorization (
  innerDerivationEquiv
  innerDerivationEquiv_refl
  innerDerivationEquiv_symm
  innerDerivationEquiv_trans
  outSetoid
  ModularFlowHomogeneousSpace
  modularFlowProjection
  outZero
  modularFlowProjection_inner_zero
  exact_sequence_inner_iff_kernel
  maurer_cartan_descent_well_defined
  maurerCartanForm
  logarithmicBridgeFactorsThroughMaurerCartan
  grand_maurer_cartan_unification_summary
)

/-! The homogeneous-space theorems remain owned by the core quotient-action
package; this surface exports them without restating their proofs. -/
export InfoGeometry.Core (
  quotientBasepoint
  smul_mk
  smul_basepoint
  stabilizer_quotientBasepoint_eq
  IsHomogeneousSpace
  quotient_isHomogeneousSpace
  exists_smul_quotientBasepoint_eq
  orbit_quotientBasepoint_univ
  cartan_fixedQuotient_isHomogeneousSpace
  stabilizer_cartan_fixedQuotientBasepoint_eq
)


export InfoGeometry.Jordan (
  logDetBarrier
  logDetBregman
)

export _root_.LogPotential (
  LogAbsVolume
  logAbsVolume_add
)

export InfoGeometry.Thermo (
  energyFromLogDet
  partitionFromLogDet
  freeEnergyFromLogDet
  freeEnergyFromLogDet_eq_neg_scale_log_partition
  freeEnergyFromLogDet_eq_internal_sub_scale_entropy
)

export LogSumExp (
  logSumExpPartition
  logSumExp
  logSumExpScaledPartition
  logSumExpScaled
  logSumExp_eq_log_partition
)

export _root_.JaynesRNMaxEnt (
  MomentFamily
  objectiveKL
  potential
  partitionFunction
  gibbsMeasure
  rnDeriv_gibbsMeasure_eq
  rnDeriv_gibbsMeasure_toReal_eq
  GibbsMinimizesKL
)

export _root_.JaynesRNMaxEnt (
  partitionFunction_pos
)

export InfoGeometry.Canonical.JaynesRNMaxEnt (
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

export MeasureProjective (
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
)

export MeasureProjective.ProjectiveState (
  normalize
  logGenerator
  logGeneratorClass
)

export InfoGeometry.MeasureProjective.Normalized (
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

export MeasureProjective (
  logPotential_smul_left_ae
  logPotential_smul_right_ae
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

export RelativePotentialCore (
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
  informationGeometricRelativeNorm
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
  informationGeometricRelativeNorm_self
  informationGeometricRelativeNorm_nonneg
  informationGeometricRelativeNorm_eq_sum_gauge_abs_neg_relativeLogDensity
  relativeInformationEnergy_self
  relativeInformationNorm_self
  relativeInformationEnergy_nonneg
  relativeInformationNorm_nonneg
  relativeInformationEnergy_eq_sum_gauge_sq_neg_relativeLogDensity
  informationGeometricRelativeNorm_scale_left
  informationGeometricRelativeNorm_scale_right
  informationGeometricRelativeNorm_scale_scale
  relativeInformationEnergy_scale_left
  relativeInformationEnergy_scale_right
  relativeInformationEnergy_scale_scale
  relativeInformationNorm_scale_left
  relativeInformationNorm_scale_right
  relativeInformationNorm_scale_scale
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
