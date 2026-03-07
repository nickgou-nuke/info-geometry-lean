import InfoGeometry.Assumptions.Determinant
import InfoGeometry.Canonical.DualConnectionsCore
import InfoGeometry.Canonical.DualConnectionsFiniteExpFamily
import InfoGeometry.Assumptions.IB
import InfoGeometry.Assumptions.LLN
import InfoGeometry.Assumptions.ManifoldDegree
import InfoGeometry.Assumptions.ManifoldHomology
import InfoGeometry.Projective.LogSum

/-!
# Axioms

Compatibility facade over `InfoGeometry.Assumptions`.
-/

namespace InfoGeometry.Axioms

export InfoGeometry.Assumptions.ManifoldDegree (
  exists_isolating_nhds_of_nondegenerate
  preimage_finite_of_regular_value
  exists_local_chart_homotopy_to_linear
  localDegreeSign
  local_degree_eq_sign_jacDet
)

export InfoGeometry.Projective (
  logSum_inequality
)

export InfoGeometry.Assumptions.IB (
  IBProblem
  KLKernel
  jointYT
  inducedMProjection
  energy
  partitionFunction
  exponentialTilt
  argmin_exponentialTilt
  ibLagrangian
  ibIteration
  ib_stationary_point_gibbs
  ib_convergence
)

export InfoGeometry.Assumptions.ManifoldHomology (
  IsRegularValue
  top_homology_is_Z
  topHomologyIso
  mappingDegree
  degree_formula_via_jacobian
)

export InfoGeometry.Assumptions.Determinant (
  detHom
  ker_det_eq_SL
  logAbsDet
  jacDet
  jacDet_comp
  jacobian_functoriality
)

universe u v

abbrev «GL» (R : Type u) (V : Type v) [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.«GL» R V

noncomputable abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.«SL» R V

export InfoGeometry.Canonical.DualConnections (
  FiberTangent
  ConnectionTensor
  fisherBilinear
  fisherBilinear_comm
  fisherBilinear_self_nonneg
  chentsovTensor
  chentsovTensor_swap_left
  alphaConnectionTensor
  eConnectionTensor
  mConnectionTensor
  alphaConnectionTensor_zero
  alphaConnectionTensor_dual_sum
  alphaConnectionTensor_dual_diff
  e_m_connection_sum
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  alphaConnection_of_finProb
  fisher_metric_eq_hessian_KL
)

export InfoGeometry.Canonical.DualConnections (
  finiteExpFamilyFinProb
  finiteExpFamilyProbMap
  fisherCovarianceBilinear
  fisherMetric_eq_covariance
  centeredScore
  fisherBilinear_eq_expectation_mul
  fisherQuadratic_eq_fisherBilinear_centeredScore
  finiteExpFamilyAlphaConnectionTensor
  finiteExpFamilyAlphaConnection
  finiteExpFamilyAlphaConnection_deformation
)

export InfoGeometry.Assumptions.LLN (
  fixed_partition_slln
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
)

end InfoGeometry.Axioms
