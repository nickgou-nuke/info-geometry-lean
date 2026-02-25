import InfoGeometry.Assumptions.Determinant
import InfoGeometry.Assumptions.DualConnections
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
  InfoGeometry.Assumptions.Determinant.GL R V

noncomputable abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :=
  InfoGeometry.Assumptions.Determinant.SL R V

export InfoGeometry.Assumptions.DualConnections (
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  fisher_metric_eq_hessian_KL
)

export InfoGeometry.Assumptions.LLN (
  fixed_partition_slln
  empirical_to_theoretical_slln
  ae_tendsto_ratio_to_rnDeriv
)

end InfoGeometry.Axioms
