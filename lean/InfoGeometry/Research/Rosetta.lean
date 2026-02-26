import InfoGeometry.Jordan.LogDet
import InfoGeometry.Thermo.FromLogDet
import InfoGeometry.Research.CayleyBregmanBridge
import InfoGeometry.Research.Attention
import InfoGeometry.Research.AttentionEuclidean
import InfoGeometry.Research.AttentionSplit
import InfoGeometry.Research.GrandUnification
import InfoGeometry.Research.FormalScaffold
import InfoGeometry.Research.GaugeUnified
import InfoGeometry.Research.SuperInference
import InfoGeometry.Research.ChiralCliffordBridge
import InfoGeometry.Research.CliffordBridge
import InfoGeometry.Research.AnomalyInflow
import InfoGeometry.Research.ChiralEinsteinBridge
import InfoGeometry.Research.ChiralGravity
import InfoGeometry.Research.ChiralTorsionBridge
import InfoGeometry.Research.BogoliubovFockSuper

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

namespace InfoGeometry.Research.Rosetta

-- Re-export stable entry points here as they mature.
-- Keep theorem statements assumption-driven (compatibility witnesses explicit).

export InfoGeometry.Research.GrandUnification (
  JordanKKTData
  IsJordanKKTGeometry
  geometry_divergence_eq_jordan_bregman
)

export InfoGeometry.Research.Cayley (
  CayleyBridge
  CayleyEquivalence
  CayleyCompatibleDualFlat
  CayleyDualFlatCompatibility
  cayleyPythagoreanInvariance
  cayleyIdentityBridge
  cayleyIdentityCompatibleGeometry
)

export InfoGeometry.Research.Attention (
  attentionWeights_sum_one
  euclideanAttentionWeights_sum_one
  lorentzianAttentionWeights_sum_one
  Vec
  Head
)

export InfoGeometry.Research.Gauge (
  Signature
  act_preserves_bilinear
)

export InfoGeometry.Research.ConformalUnification.ConformalInference (
  P
  K
  D
  P_D
  P_MP
  spectralChiralProjector
  metricChiralProjector
  chiralAnomaly
  chiralAnomalyOperator
  epsilon
  chiralScale
  ProjectorCommutationClosure
  chiral_commutation_link
  chiralAnomaly_eq_zero_iff_projectorCommutation
  IsNormalInference
  IsChiralInference
  NormalInferenceState
  ChiralInferenceState
)

export InfoGeometry.Research.SuperInference (
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

export InfoGeometry.Research.ChiralCliffordBridge (
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

export InfoGeometry.Research.CliffordBridge (
  splitQuadratic_eq_gaugeQuadratic
  splitBilinear_eq_gaugeBilinear
  q_agrees_with_Gauge_quad
  B_agrees_with_Gauge_bilinear
)

export InfoGeometry.Research.ChiralTorsionBridge (
  boltzmannRelativeVolumeEntropy
  boltzmannRelativeVolumeEntropy_eq_divergence
  gibbsSmoothingOnGeneralizedKL
  gibbsSmoothingOnGeneralizedKL_pos
  IsVacuumApexNull
  vacuumApexTwistor
  ChiralTorsionChentsovGibbsState
  chentsov_and_gibbs_of_state
  ChiralTorsionChentsovGibbsBridge
  torsion_nonzero_of_chiral
  chentsov_and_gibbs_of_bridge
)

export InfoGeometry.Research.AnomalyInflow (
  variationChernSimons
  bulkChernSimonsVariation
  boundaryAnomaly
  boundaryAnomalyDensity
  AnomalyInflowClosure
  anomalyInflowClosure
  anomaly_inflow_cancellation
)

export InfoGeometry.Research.ChiralEinsteinBridge (
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

export InfoGeometry.Research.ChiralGravity (
  anomalyEinsteinResidualAt
  AnomalyCurvatureForcingStateAt
  anomalyEinsteinResidual_eq_kappa_mul_metric
  anomaly_nonzero_forces_curved_plus_component
  anomaly_nonzero_excludes_vacuum
  routingAnomaly_nonzero_forces_curved_plus_component
)

export InfoGeometry.Research.BogoliubovFockSuper (
  BogoliubovParams
  BogoliubovMixingParams
  FockEnd
  FockEndomorphism
  bogoliubovAnnihilation
  bogoliubovCreation
  numberOperator
  bogoliubovNumberOperator
  grandCanonicalGenerator
  grandCanonicalFockGenerator
  grandCanonicalEulerStep
  grandCanonicalFockEulerStep
  SuperParity
  paritySign
  superBracket
  fockSuperBracket
  commutator
  fockCommutator
  anticommutator
  fockAnticommutator
  CARWitness
  CARClosure
  CCRWitness
  CCRClosure
  anticommutator_symm
  fockAnticommutator_symm
  commutator_swap
  fockCommutator_swap
  superBracket_bogoliubov_covariance
  anticommutator_bogoliubov_of_CAR
  commutator_bogoliubov_of_CCR
  inducedChemicalPotential
  einsteinInducedChemicalPotential
  einsteinFockDeformation
  einsteinFockDeformationOperator
  grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported
  grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
)

end InfoGeometry.Research.Rosetta
