import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
import InfoGeometry.Krein.Prelude
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge

Adjacency bridge from the corrected phase-space generalized-metric owner to the
existing doubled-space chirality projectors.

This file stays narrow, but it is no longer untwisted-only:

- it records the `B`-twisted realized polarization and its realized `±`
  projectors on the doubled carrier,
- it keeps the untwisted (`ofMetric`) realization as a special case,
- and it does not identify the phase-space generalized-metric involution with
  the doubled spectral-sign involution.

So the corrected owner is attached to the maintained doubled-space corridor
without collapsing distinct ontologies, while still exposing the full
generalized-metric projector transport.
-/

namespace InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum
open InfoGeometry.Krein

section DoubledLinear

variable {E : Type*}
variable [NormedAddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
@[simp] lemma to_doubled_add (x₁ x₂ y₁ y₂ : E) :
    (to_doubled (x₁ + x₂) (y₁ + y₂) : DoubledSpace E)
      = to_doubled x₁ y₁ + to_doubled x₂ y₂ := by
  apply DoubledSpace.ext <;> simp [to_doubled]

@[simp] lemma to_doubled_smul (r : ℝ) (x y : E) :
    (to_doubled (r • x) (r • y) : DoubledSpace E)
      = r • to_doubled x y := by
  apply DoubledSpace.ext <;> simp [to_doubled]

@[simp] lemma to_doubled_neg (x y : E) :
    (to_doubled (-x) (-y) : DoubledSpace E) = -to_doubled x y := by
  simpa using (to_doubled_smul (r := (-1 : ℝ)) x y)

@[simp] lemma to_doubled_sub (x₁ x₂ y₁ y₂ : E) :
    (to_doubled (x₁ - x₂) (y₁ - y₂) : DoubledSpace E)
      = to_doubled x₁ y₁ - to_doubled x₂ y₂ := by
  simp [sub_eq_add_neg]

end DoubledLinear

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] lemma fromDoubledCopyRho_toDoubledCopyRho
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : PhaseSpaceCarrier E) :
    fromDoubledCopyRho (E := E) ρ (toDoubledCopyRho (E := E) ρ X) = X := by
  change (doubledCopyRhoEquiv (E := E) ρ).symm ((doubledCopyRhoEquiv (E := E) ρ) X) = X
  exact (doubledCopyRhoEquiv (E := E) ρ).symm_apply_apply X

@[simp] lemma toDoubledCopyRho_fromDoubledCopyRho
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) (X : DoubledSpace E) :
    toDoubledCopyRho (E := E) ρ (fromDoubledCopyRho (E := E) ρ X) = X := by
  change (doubledCopyRhoEquiv (E := E) ρ) ((doubledCopyRhoEquiv (E := E) ρ).symm X) = X
  exact (doubledCopyRhoEquiv (E := E) ρ).apply_symm_apply X

/-- The realized `B`-transform on the doubled carrier under a chosen duality
equivalence. -/
@[rep_depth krein]
noncomputable def realizedBTransform
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (DoubledSpace E) :=
  (toDoubledCopyRho (E := E) ρ).comp (G.bTransform)
    |>.comp (fromDoubledCopyRho (E := E) ρ)

/-- The realized inverse `B`-transform on the doubled carrier. -/
@[rep_depth krein]
noncomputable def realizedBTransformInv
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (DoubledSpace E) :=
  (toDoubledCopyRho (E := E) ρ).comp (G.bTransformInv)
    |>.comp (fromDoubledCopyRho (E := E) ρ)

/-- The realized generalized-metric polarization on the doubled carrier. -/
@[rep_depth krein]
noncomputable def realizedPolarization
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (DoubledSpace E) :=
  (toDoubledCopyRho (E := E) ρ).comp (G.polarization)
    |>.comp (fromDoubledCopyRho (E := E) ρ)

/-- The realized `+1` projector on the doubled carrier induced by a
generalized-metric datum. -/
@[rep_depth krein]
noncomputable def realizedPlusProjector
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (DoubledSpace E) :=
  InfoGeometry.Cartan.Pplus (realizedPolarization (G := G) ρ)

/-- The realized `-1` projector on the doubled carrier induced by a
generalized-metric datum. -/
@[rep_depth krein]
noncomputable def realizedMinusProjector
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (DoubledSpace E) :=
  InfoGeometry.Cartan.Pminus (realizedPolarization (G := G) ρ)

/-- Realized polarization as conjugation of the phase-space polarization. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_polarization_eq_realized
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (G.polarization)
      = (realizedPolarization (G := G) ρ).comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  simp [realizedPolarization, LinearMap.comp_apply]

/-- Realized `B`-transform as conjugation of the phase-space `B`-transform. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_bTransform_eq_realized
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (G.bTransform)
      = (realizedBTransform (G := G) ρ).comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  simp [realizedBTransform, LinearMap.comp_apply]

/-- Realized inverse `B`-transform as conjugation of the phase-space inverse. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_bTransformInv_eq_realized
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (G.bTransformInv)
      = (realizedBTransformInv (G := G) ρ).comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  simp [realizedBTransformInv, LinearMap.comp_apply]

/-- The realized polarization is the `B`-twisted conjugate of the doubled
chirality involution. -/
@[rep_depth krein] theorem realizedPolarization_eq_b_conj_modular_j
    (G : GeneralizedMetricDatum E) :
    realizedPolarization (G := G) G.metric.gFlat
      = realizedBTransform (G := G) G.metric.gFlat * (modular_j (E := E)).toLinearMap
          * realizedBTransformInv (G := G) G.metric.gFlat := by
  apply LinearMap.ext
  intro X
  have hphaseJ :
      (toDoubledCopyRho (E := E) G.metric.gFlat).comp (phaseJ G.metric.gFlat)
        = (modular_j (E := E)).toLinearMap.comp
            (toDoubledCopyRho (E := E) G.metric.gFlat) := by
      simpa using (toDoubledCopyRho_comp_phaseJ (E := E) (ρ := G.metric.gFlat))
  calc
    realizedPolarization (G := G) G.metric.gFlat X
        = (toDoubledCopyRho (E := E) G.metric.gFlat)
            (G.polarization (fromDoubledCopyRho (E := E) G.metric.gFlat X)) := by
            simp [realizedPolarization, LinearMap.comp_apply]
    _ = (toDoubledCopyRho (E := E) G.metric.gFlat)
          (G.bTransform (phaseJ G.metric.gFlat
            (G.bTransformInv (fromDoubledCopyRho (E := E) G.metric.gFlat X)))) := by
          simp [polarization_eq_b_conj_phaseJ (G := G)]
    _ = (realizedBTransform (G := G) G.metric.gFlat)
          ((modular_j (E := E)).toLinearMap
            ((realizedBTransformInv (G := G) G.metric.gFlat) X)) := by
          simp [realizedBTransform, realizedBTransformInv, LinearMap.comp_apply]

/-- The `+1` phase-space projector realizes as the `+1` projector of the
`B`-twisted doubled polarization. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_plusProjector_eq_realized
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (G.plusProjector)
      = (realizedPlusProjector (G := G) ρ).comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  have hpol :
      (toDoubledCopyRho (E := E) ρ) (G.polarization X)
        = (realizedPolarization (G := G) ρ) (toDoubledCopyRho (E := E) ρ X) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
        (toDoubledCopyRho_comp_polarization_eq_realized (G := G) ρ)
  have hpol' :
      to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2)
        = (realizedPolarization (G := G) ρ)
            (to_doubled X.1 (ρ.symm X.2)) := by
    simpa [toDoubledCopyRho_apply] using hpol
  calc
    (toDoubledCopyRho (E := E) ρ) (G.plusProjector X)
        = (2 : ℝ)⁻¹ •
            (to_doubled X.1 (ρ.symm X.2)
              + to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2)) := by
              simp [GeneralizedMetricDatum.plusProjector, InfoGeometry.Cartan.Pplus,
                toDoubledCopyRho_apply]
    _ = (2 : ℝ)⁻¹ • to_doubled X.1 (ρ.symm X.2)
          + (2 : ℝ)⁻¹ • to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2) := by
          simp [smul_add]
    _ = (2 : ℝ)⁻¹ • to_doubled X.1 (ρ.symm X.2)
          + (2 : ℝ)⁻¹ • (realizedPolarization (G := G) ρ)
              (to_doubled X.1 (ρ.symm X.2)) := by
          simp [hpol']
    _ = (realizedPlusProjector (G := G) ρ) (toDoubledCopyRho (E := E) ρ X) := by
          simp [realizedPlusProjector, InfoGeometry.Cartan.Pplus, toDoubledCopyRho_apply, smul_add]

/-- The `-1` phase-space projector realizes as the `-1` projector of the
`B`-twisted doubled polarization. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_minusProjector_eq_realized
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    (toDoubledCopyRho (E := E) ρ).comp (G.minusProjector)
      = (realizedMinusProjector (G := G) ρ).comp (toDoubledCopyRho (E := E) ρ) := by
  apply LinearMap.ext
  intro X
  have hpol :
      (toDoubledCopyRho (E := E) ρ) (G.polarization X)
        = (realizedPolarization (G := G) ρ) (toDoubledCopyRho (E := E) ρ X) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
        (toDoubledCopyRho_comp_polarization_eq_realized (G := G) ρ)
  have hpol' :
      to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2)
        = (realizedPolarization (G := G) ρ)
            (to_doubled X.1 (ρ.symm X.2)) := by
    simpa [toDoubledCopyRho_apply] using hpol
  calc
    (toDoubledCopyRho (E := E) ρ) (G.minusProjector X)
        = (2 : ℝ)⁻¹ •
            (to_doubled X.1 (ρ.symm X.2)
              - to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2)) := by
              simp [GeneralizedMetricDatum.minusProjector, InfoGeometry.Cartan.Pminus,
                toDoubledCopyRho_apply, to_doubled_sub]
    _ = (2 : ℝ)⁻¹ • to_doubled X.1 (ρ.symm X.2)
          + -((2 : ℝ)⁻¹ • to_doubled (G.polarization X).1 (ρ.symm (G.polarization X).2)) := by
          simp [sub_eq_add_neg, smul_add]
    _ = (2 : ℝ)⁻¹ • to_doubled X.1 (ρ.symm X.2)
          + -((2 : ℝ)⁻¹ • (realizedPolarization (G := G) ρ)
              (to_doubled X.1 (ρ.symm X.2))) := by
          simp [hpol']
    _ = (realizedMinusProjector (G := G) ρ) (toDoubledCopyRho (E := E) ρ X) := by
          simp [realizedMinusProjector, InfoGeometry.Cartan.Pminus, toDoubledCopyRho_apply,
            sub_eq_add_neg, smul_add]

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
