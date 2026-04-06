import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
import InfoGeometry.Krein.Prelude
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge

Adjacency bridge from the corrected phase-space generalized-metric owner to the
existing doubled-space chirality projectors.

This file stays narrow:

- it does not identify the phase-space generalized-metric involution with the
  doubled spectral-sign involution,
- instead, it records the exact untwisted realization into the doubled
  chirality (`J`) projector surface,
- so the corrected owner is attached to an existing maintained doubled-space
  corridor without collapsing distinct ontologies.
-/

namespace InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The untwisted phase-space `+1` projector realizes exactly as the doubled
chirality `+1` projector. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_ofMetric_plusProjector
    (metric : MetricDatum E) :
    (toDoubledCopyRho metric.gFlat).comp ((ofMetric metric).plusProjector)
      = (gradePlusProj (E := E)).toLinearMap.comp (toDoubledCopyRho metric.gFlat) := by
  apply LinearMap.ext
  intro X
  have hpol :
      (toDoubledCopyRho metric.gFlat) ((ofMetric metric).polarization X)
        = modular_j (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
        (toDoubledCopyRho_comp_ofMetricPolarization (E := E) metric)
  rw [GeneralizedMetricDatum.plusProjector, InfoGeometry.Cartan.Pplus, gradePlusProj]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.map_smul, LinearMap.map_add, Module.End.one_apply]
  rw [hpol]
  rfl

/-- The untwisted phase-space `-1` projector realizes exactly as the doubled
chirality `-1` projector. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_ofMetric_minusProjector
    (metric : MetricDatum E) :
    (toDoubledCopyRho metric.gFlat).comp ((ofMetric metric).minusProjector)
      = (gradeMinusProj (E := E)).toLinearMap.comp (toDoubledCopyRho metric.gFlat) := by
  apply LinearMap.ext
  intro X
  have hpol :
      (toDoubledCopyRho metric.gFlat) ((ofMetric metric).polarization X)
        = modular_j (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
        (toDoubledCopyRho_comp_ofMetricPolarization (E := E) metric)
  rw [GeneralizedMetricDatum.minusProjector, InfoGeometry.Cartan.Pminus, gradeMinusProj]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.map_smul, LinearMap.map_sub, Module.End.one_apply]
  rw [hpol]
  rfl

/-- Under a Riesz compatibility law for the metric datum, the untwisted owner
generalized metric realizes as the ambient Hilbert inner product on the doubled
carrier. -/
@[rep_depth krein] theorem ofMetric_generalizedMetricForm_eq_doubledInner
    (metric : MetricDatum E)
    (hmetric : ∀ x y : E, metric.gFlat x y = ⟪x, y⟫_ℝ)
    (X Y : PhaseSpaceCarrier E) :
    (ofMetric metric).generalizedMetricForm X Y
      = ⟪toDoubledCopyRho metric.gFlat X, toDoubledCopyRho metric.gFlat Y⟫_ℝ := by
  rcases X with ⟨x, φ⟩
  rcases Y with ⟨y, ψ⟩
  have hdual :
      φ (metric.gFlat.symm ψ)
        = ⟪metric.gFlat.symm φ, metric.gFlat.symm ψ⟫_ℝ := by
    calc
      φ (metric.gFlat.symm ψ)
          = metric.gFlat (metric.gFlat.symm φ) (metric.gFlat.symm ψ) := by
              simp
      _ = ⟪metric.gFlat.symm φ, metric.gFlat.symm ψ⟫_ℝ := hmetric _ _
  rw [GeneralizedMetricDatum.generalizedMetricForm_ofMetric_apply]
  simp [toDoubledCopyRho_apply, WithLp.prod_inner_apply, hmetric x y, hdual]

/-- The doubled chirality difference recovers the chirality involution `J`. -/
@[rep_depth krein] theorem chiralityDifference_eq_modular_j :
    ((gradePlusProj (E := E) - gradeMinusProj (E := E)).toLinearMap)
      = (modular_j (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [gradePlusProj, gradeMinusProj, modular_j_apply, sub_eq_add_neg,
      add_left_comm, add_comm, smul_add]
  all_goals
    rw [← add_smul]
    norm_num

/-- The untwisted owner involution `S = P₊ - P₋` realizes as the doubled
chirality difference `gradePlusProj - gradeMinusProj`. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_ofMetric_polarization_eq_chiralityDifference
    (metric : MetricDatum E) :
    (toDoubledCopyRho metric.gFlat).comp ((ofMetric metric).polarization)
      = ((gradePlusProj (E := E) - gradeMinusProj (E := E)).toLinearMap).comp
          (toDoubledCopyRho metric.gFlat) := by
  rw [chiralityDifference_eq_modular_j]
  exact toDoubledCopyRho_comp_ofMetricPolarization (E := E) metric

section RealizedFixpoints

variable [CompleteSpace E]

/-- The realized image of the untwisted phase-space `+1` projector is fixed by
the doubled chirality `+1` projector. -/
@[rep_depth krein, simp] theorem ofMetric_plusProjector_realized_is_chiralityPlus_fixed
    (metric : MetricDatum E) (X : PhaseSpaceCarrier E) :
    gradePlusProj (E := E) ((toDoubledCopyRho metric.gFlat) ((ofMetric metric).plusProjector X))
      = (toDoubledCopyRho metric.gFlat) ((ofMetric metric).plusProjector X) := by
  have hmap :=
    congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_ofMetric_plusProjector metric)
  have hmap' :
      (toDoubledCopyRho metric.gFlat) ((ofMetric metric).plusProjector X)
        = gradePlusProj (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
    simpa [LinearMap.comp_apply] using hmap
  have hid :=
    congrArg
      (fun F : DoubledSpace E →L[ℝ] DoubledSpace E => F ((toDoubledCopyRho metric.gFlat) X))
      (gradePlusProj_idempotent (E := E))
  calc
    gradePlusProj (E := E) ((toDoubledCopyRho metric.gFlat) ((ofMetric metric).plusProjector X))
        = gradePlusProj (E := E) (gradePlusProj (E := E) ((toDoubledCopyRho metric.gFlat) X)) := by
            rw [hmap']
    _ = gradePlusProj (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
          simpa [ContinuousLinearMap.comp_apply] using hid
    _ = (toDoubledCopyRho metric.gFlat) ((ofMetric metric).plusProjector X) := by
          rw [hmap']

/-- The realized image of the untwisted phase-space `-1` projector is fixed by
the doubled chirality `-1` projector. -/
@[rep_depth krein, simp] theorem ofMetric_minusProjector_realized_is_chiralityMinus_fixed
    (metric : MetricDatum E) (X : PhaseSpaceCarrier E) :
    gradeMinusProj (E := E) ((toDoubledCopyRho metric.gFlat) ((ofMetric metric).minusProjector X))
      = (toDoubledCopyRho metric.gFlat) ((ofMetric metric).minusProjector X) := by
  have hmap :=
    congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_ofMetric_minusProjector metric)
  have hmap' :
      (toDoubledCopyRho metric.gFlat) ((ofMetric metric).minusProjector X)
        = gradeMinusProj (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
    simpa [LinearMap.comp_apply] using hmap
  have hid :=
    congrArg
      (fun F : DoubledSpace E →L[ℝ] DoubledSpace E => F ((toDoubledCopyRho metric.gFlat) X))
      (gradeMinusProj_idempotent (E := E))
  calc
    gradeMinusProj (E := E) ((toDoubledCopyRho metric.gFlat) ((ofMetric metric).minusProjector X))
        = gradeMinusProj (E := E) (gradeMinusProj (E := E) ((toDoubledCopyRho metric.gFlat) X)) := by
            rw [hmap']
    _ = gradeMinusProj (E := E) ((toDoubledCopyRho metric.gFlat) X) := by
          simpa [ContinuousLinearMap.comp_apply] using hid
    _ = (toDoubledCopyRho metric.gFlat) ((ofMetric metric).minusProjector X) := by
          rw [hmap']

end RealizedFixpoints

end Core

end InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
