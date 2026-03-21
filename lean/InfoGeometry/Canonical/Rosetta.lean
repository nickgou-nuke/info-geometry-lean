import InfoGeometry.Canonical.LogDet
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
import InfoGeometry.Canonical.ChiralTorsionBridge
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.WeylInformationGauge
import InfoGeometry.Canonical.WeylGaugeField
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.WeylTransportChiralBridge
import InfoGeometry.Canonical.WilsonLoop
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.ModularSpinorBridge
import InfoGeometry.Canonical.Twistor
import InfoGeometry.Canonical.BerryPhase
import InfoGeometry.Canonical.Singular
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
  geometry_divergence_eq_jordan_bregman
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
  NormalInferenceState
  ChiralInferenceState
)

export InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra (
  SatisfiesPWeight
  SatisfiesKWeight
  SatisfiesMasterRelation
  SatisfiesFlatWeights
  ConformalWeightClosure
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

export InfoGeometry.Canonical.WeylInformationGauge (
  cartanWeyl_generator_split
  cartanWeyl_dilation_sources_transportedEinsteinResidual
  cartanWeyl_dilation_sources_transportedEinsteinResidual_of_parts
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
  toGeneratedFlow
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
  finiteSumIntegrator_integrate_eq
  finiteSumIntegrator_integrateConnection_eq_sum
  finiteSumIntegrator_holonomy_eq_sum
  finiteSumIntegrator_integrateCurvature_eq_sum
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

export InfoGeometry.Canonical.ModularSpinorBridge (
  spinorBilinear
  weakValueNumerator
  weakValueDenominator
  weakValue
  weakValueNumerator_modularConjugate_eq_spinorBilinear
  weakValue_modularConjugate_eq_spinorBilinear_div_overlap
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

section ModularCPTRosetta

open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Quantum.ModularAnomaly

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E)

noncomputable local instance : NormedAddCommGroup Xc := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : NormedSpace ℝ Xc := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : CompleteSpace Xc := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

/--
In the concrete real-Majorana doubled model, the legacy modular axis
`modularComplexI` is exactly the internal split-Clifford axis `K = J ∘ ε`.
-/
@[simp] theorem modularComplexI_toLinearMap_eq_realMajoranaKAxis :
    (modularComplexI (E := E)).toLinearMap =
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E).K := by
  rfl

/--
Scalar bridge: the conformal source tension is presented as the transported
Einstein residual under the explicit Ricci transport interface.
-/
theorem sourceTension_eq_transportedEinsteinResidual
    (CBA : ConformalBeliefAlgebra E)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale) :
    CBA.CI.chiralScale =
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ := by
  simpa [eq_comm] using hSource

/--
Operator-source bridge: the transported Einstein residual is exactly the scalar
chemical-potential source used in the Bogoliubov/Fock layer.
-/
@[simp] theorem transportedEinsteinResidual_eq_einsteinInducedChemicalPotential
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V) :
    InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ =
      einsteinInducedChemicalPotential R K x scalar Λ V Γ := by
  rfl

/--
The Einstein-induced chemical potential lifts to the Fock layer as the scalar
identity deformation operator.
-/
@[simp] theorem einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V) :
    einsteinFockDeformationOperator R K x scalar Λ V Γ =
      einsteinInducedChemicalPotential R K x scalar Λ V Γ
        • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  rfl

/--
Modular presentation: under the concrete shadow realization, the modular anomaly
is the commutator presentation of the transported source tension.
-/
theorem modularAnomalyGenerator_eq_commutator_of_transport_source
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    M.modularAnomalyGenerator U =
      (U.symm : Xc →L[ℝ] Xc).comp
        (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  exact InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.modularAnomalyGenerator_eq_concrete_commutator_shadow
    (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U)

/--
Facade theorem packaging the three checked presentations of the same source
surface: scalar transport, chemical-potential lift, and modular commutator
shadow.
-/
theorem rosetta_source_tension_three_presentations
    [FiniteDimensional ℝ E]
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0)
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    modularComplexI (E := E) = InfoGeometry.Krein.dilationOperator (E := E) ∧
      CBA.IsVolumePreservingPart CBA.M ∧
      CBA.IsWeylDilationPart CBA.D ∧
      CBA.CI.chiralScale =
        InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ∧
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ =
          einsteinInducedChemicalPotential R K x scalar Λ V Γ ∧
      einsteinFockDeformationOperator R K x scalar Λ V Γ =
        einsteinInducedChemicalPotential R K x scalar Λ V Γ
          • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) ∧
      M.modularAnomalyGenerator U =
        (U.symm : Xc →L[ℝ] Xc).comp
          (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  have hWeyl :
      CBA.IsVolumePreservingPart CBA.M
        ∧ CBA.IsWeylDilationPart CBA.D
        ∧ InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
            (scalar := scalar) (Λ := Λ) V Γ ≠ 0 :=
    cartanWeyl_dilation_sources_transportedEinsteinResidual
      (CBA := CBA) (hCartan := hCartan) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hSource hAnom
  rcases hWeyl with ⟨hM, hD, _hResidual⟩
  refine ⟨modularComplexI_eq_dilationOperator (E := E), hM, hD, ?_, ?_, ?_, ?_⟩
  · exact sourceTension_eq_transportedEinsteinResidual
      (CBA := CBA) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hSource
  · exact transportedEinsteinResidual_eq_einsteinInducedChemicalPotential
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
  · exact einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
  · exact modularAnomalyGenerator_eq_commutator_of_transport_source
      (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U)

/--
Compatibility wrapper preserving the earlier Rosetta capstone surface while now
factoring through the explicit helper theorem family above.
-/
theorem modularCPT_source_rosetta
    [FiniteDimensional ℝ E]
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0)
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    modularComplexI (E := E) = InfoGeometry.Krein.dilationOperator (E := E) ∧
      CBA.IsVolumePreservingPart CBA.M ∧
      CBA.IsWeylDilationPart CBA.D ∧
      einsteinInducedChemicalPotential R K x scalar Λ V Γ ≠ 0 ∧
      M.modularAnomalyGenerator U =
        (U.symm : Xc →L[ℝ] Xc).comp
          (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  have hWeyl :
      CBA.IsVolumePreservingPart CBA.M
        ∧ CBA.IsWeylDilationPart CBA.D
        ∧ InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
            (scalar := scalar) (Λ := Λ) V Γ ≠ 0 :=
    cartanWeyl_dilation_sources_transportedEinsteinResidual
      (CBA := CBA) (hCartan := hCartan) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hSource hAnom
  rcases hWeyl with ⟨hM, hD, hResidual⟩
  have hPack := rosetta_source_tension_three_presentations
    (CBA := CBA) (hCartan := hCartan) (R := R) (K := K) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
    (hSource := hSource) (hAnom := hAnom)
    (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U)
  rcases hPack with ⟨hKAxis, _hM, _hD, _hSourceEq, hμEq, _hLiftEq, hMod⟩
  refine ⟨hKAxis, hM, hD, ?_, hMod⟩
  simpa [hμEq] using hResidual


section WeylScaleKkRosetta

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Krein

variable {I F A P : Type*}
variable [Group P]
variable {H A₀ B₀ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]

/--
Endomorphism-valued shadow of a Weyl scale-transport observable along a chosen
real parameterization.
-/
noncomputable def weylScaleTransportShadow
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I) :
    ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H :=
  fun s => realize <|
    ScaleEquivariantFlow.transportObservable Ξ phaseOf (path 0) (path s)

/-- Pointwise expansion of `weylScaleTransportShadow`. -/
@[simp] theorem weylScaleTransportShadow_apply
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (s : ℝ) :
    weylScaleTransportShadow (H := H) Ξ phaseOf realize path s =
      realize (ScaleEquivariantFlow.transportObservable Ξ phaseOf (path 0) (path s)) := by
  rfl

/--
If a Weyl scale-transport shadow acts injectively on the carrier and transports
both chiral slices to the baseline through the Clifford label action, then it
instantiates the modular/Clifford transport hypothesis used by the analytical
index layer.
-/
theorem weylScaleTransportShadow_to_modularCliffordTransport
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    ChiralSliceModularCliffordTransportAlong
      (D := D) (Γ := Γ)
      (weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
      clAct unit := by
  exact ⟨hUnit, hShadowInj, hPlusMap, hMinusMap⟩

/--
Weyl scale transport yields analytical-index invariance once its endomorphism
shadow satisfies the modular/Clifford slice-transport requirements.
-/
theorem indexInvariantAlong_of_weylScaleTransport
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_modularCliffordTransport
    (D := D) (Γ := Γ)
    (σ := weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
    (clAct := clAct)
    (unit := unit)
    (weylScaleTransportShadow_to_modularCliffordTransport
      (H := H)
      (Ξ := Ξ) (phaseOf := phaseOf) (realize := realize) (path := path)
      (D := D) (Γ := Γ)
      (clAct := clAct) (unit := unit)
      hUnit hShadowInj hPlusMap hMinusMap)

/--
KK analytical-index bridge specialized to a Weyl scale-transport shadow.
This is the missing Rosetta step from the Weyl/scale lane into the modular /
Clifford / KK invariance theorem surface.
-/
theorem kk_analyticalIndex_eq_of_weylScaleTransport
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H] [KreinGradedModule H]
    (Xk : InfoGeometry.KK.KasparovCycle A₀ B₀ H)
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hD0 : D 0 = Xk.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        Xk.analyticalIndex := by
  exact InfoGeometry.KK.analyticalIndex_eq_of_modularCliffordTransport
    (X := Xk)
    (D := D)
    (Γ := Γ)
    (σ := weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
    (clAct := clAct)
    (unit := unit)
    hD0
    hΓ0
    (weylScaleTransportShadow_to_modularCliffordTransport
      (H := H)
      (Ξ := Ξ) (phaseOf := phaseOf) (realize := realize) (path := path)
      (D := D) (Γ := Γ)
      (clAct := clAct) (unit := unit)
      hUnit hShadowInj hPlusMap hMinusMap)

end WeylScaleKkRosetta


section WeylScaleJordanRosetta

variable {I F A P E : Type*}
variable [Group P]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Scalar readout of a Weyl scale-transport observable. -/
noncomputable def weylScaleTransportScalarShadow
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ) :
    I → I → ℝ :=
  fun i j => scalarOf (ScaleEquivariantFlow.transportObservable Ξ phaseOf i j)

/-- Pointwise expansion of `weylScaleTransportScalarShadow`. -/
@[simp] theorem weylScaleTransportScalarShadow_apply
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (i j : I) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf i j =
      scalarOf (ScaleEquivariantFlow.transportObservable Ξ phaseOf i j) := by
  rfl

/--
If a Weyl scale-transport scalar shadow agrees with the dual-flat divergence,
then any Jordan/KKT realization of that divergence reads the same shadow as the
Jordan Bregman divergence.
-/
theorem weylScaleTransportScalarShadow_eq_jordanBregman_of_isJordanKKTGeometry
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (S : InfoGeometry.Geometry.DualFlat.DualFlatStructure E)
    (hJG : IsJordanKKTGeometry J S)
    (hShadowDiv : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        InfoGeometry.Geometry.DualFlat.divergence S x y) :
    ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y := by
  intro x y
  rw [hShadowDiv x y]
  exact InfoGeometry.Canonical.GrandUnification.geometry_divergence_eq_jordan_bregman
    (J := J) (S := S) hJG x y

/--
Conversely, if the same Weyl scale-transport shadow reads both the dual-flat
Divergence and the Jordan Bregman divergence, it furnishes the full
Jordan/KKT geometry witness.
-/
theorem isJordanKKTGeometry_of_weylScaleTransportShadow
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (S : InfoGeometry.Geometry.DualFlat.DualFlatStructure E)
    (hShadowDiv : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        InfoGeometry.Geometry.DualFlat.divergence S x y)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y) :
    IsJordanKKTGeometry J S := by
  intro x y
  rw [← hShadowDiv x y, hShadowJ x y]

/-- Transported scalar shadow vanishes on the diagonal in the Jordan/KKT lane. -/
@[simp] theorem weylScaleTransportScalarShadow_self_eq_zero_of_jordanBregman
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x : E) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf x) = 0 := by
  rw [hShadowJ x x]
  exact J.DBregman_self x

/-- Transported scalar shadow is nonnegative in the Jordan/KKT lane. -/
theorem weylScaleTransportScalarShadow_nonneg_of_jordanBregman
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y : E) :
    0 ≤ weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) := by
  rw [hShadowJ x y]
  exact J.DBregman_nonneg x y

/-- Transported scalar shadow detects equality in the Jordan/KKT lane. -/
theorem weylScaleTransportScalarShadow_eq_zero_iff_of_jordanBregman
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y : E) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) = 0 ↔ x = y := by
  rw [hShadowJ x y]
  exact J.DBregman_eq_zero_iff x y

/--
The generalized Pythagorean law transports from Jordan/KKT geometry to the
Weyl scale shadow once the shadow reads the Jordan Bregman divergence.
-/
theorem weylScaleTransportScalarShadow_generalized_pythagorean_of_jordanBregman
    (Ξ : ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y z : E)
    (hOrth : J.IsBregmanOrthogonal x y z) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y)
      + weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf y) (indexOf z)
      = weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf z) := by
  rw [hShadowJ x y, hShadowJ y z, hShadowJ x z]
  exact J.generalized_pythagorean_theorem x y z hOrth

end WeylScaleJordanRosetta

end ModularCPTRosetta

end InfoGeometry.Canonical.Rosetta
