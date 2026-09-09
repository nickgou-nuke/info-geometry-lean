import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
import Mathlib.LinearAlgebra.BilinearForm.Hom
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

/-! The intertwining equations upgrade to operator equalities because the
    soldering map is an equivalence. -/

@[rep_depth krein] theorem realized_ofMetric_polarization_eq_modular_j
    (metric : MetricDatum E) :
    realizedPolarization (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
      = (modular_j (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro Y
  let X : PhaseSpaceCarrier E :=
    fromDoubledCopyRho (E := E) metric.gFlat Y
  have hXY : toDoubledCopyRho (E := E) metric.gFlat X = Y := by
    simpa [X] using
      (toDoubledCopyRho_fromDoubledCopyRho (E := E) metric.gFlat Y)
  have hrealized := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_polarization_eq_realized
        (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat)
  have hmetric := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_ofMetricPolarization metric)
  calc
    realizedPolarization (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat Y
        = realizedPolarization (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
            (toDoubledCopyRho (E := E) metric.gFlat X) := by rw [hXY]
    _ = toDoubledCopyRho (E := E) metric.gFlat
          ((GeneralizedMetricDatum.ofMetric metric).polarization X) := by
          simpa [LinearMap.comp_apply] using hrealized.symm
    _ = modular_j (E := E) (toDoubledCopyRho (E := E) metric.gFlat X) := by
          simpa [LinearMap.comp_apply] using hmetric
    _ = modular_j (E := E) Y := by rw [hXY]

@[rep_depth krein] theorem realized_ofMetric_plusProjector_eq_gradePlusProj
    (metric : MetricDatum E) :
    realizedPlusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
      = (gradePlusProj (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro Y
  let X : PhaseSpaceCarrier E :=
    fromDoubledCopyRho (E := E) metric.gFlat Y
  have hXY : toDoubledCopyRho (E := E) metric.gFlat X = Y := by
    simpa [X] using
      (toDoubledCopyRho_fromDoubledCopyRho (E := E) metric.gFlat Y)
  have hrealized := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized
        (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat)
  have hmetric := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_ofMetric_plusProjector metric)
  calc
    realizedPlusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat Y
        = realizedPlusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
            (toDoubledCopyRho (E := E) metric.gFlat X) := by rw [hXY]
    _ = toDoubledCopyRho (E := E) metric.gFlat
          ((GeneralizedMetricDatum.ofMetric metric).plusProjector X) := by
          simpa [LinearMap.comp_apply] using hrealized.symm
    _ = gradePlusProj (E := E)
          (toDoubledCopyRho (E := E) metric.gFlat X) := by
          simpa [LinearMap.comp_apply] using hmetric
    _ = gradePlusProj (E := E) Y := by rw [hXY]

@[rep_depth krein] theorem realized_ofMetric_minusProjector_eq_gradeMinusProj
    (metric : MetricDatum E) :
    realizedMinusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
      = (gradeMinusProj (E := E)).toLinearMap := by
  apply LinearMap.ext
  intro Y
  let X : PhaseSpaceCarrier E :=
    fromDoubledCopyRho (E := E) metric.gFlat Y
  have hXY : toDoubledCopyRho (E := E) metric.gFlat X = Y := by
    simpa [X] using
      (toDoubledCopyRho_fromDoubledCopyRho (E := E) metric.gFlat Y)
  have hrealized := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_minusProjector_eq_realized
        (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat)
  have hmetric := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_ofMetric_minusProjector metric)
  calc
    realizedMinusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat Y
        = realizedMinusProjector (G := GeneralizedMetricDatum.ofMetric metric) metric.gFlat
            (toDoubledCopyRho (E := E) metric.gFlat X) := by rw [hXY]
    _ = toDoubledCopyRho (E := E) metric.gFlat
          ((GeneralizedMetricDatum.ofMetric metric).minusProjector X) := by
          simpa [LinearMap.comp_apply] using hrealized.symm
    _ = gradeMinusProj (E := E)
          (toDoubledCopyRho (E := E) metric.gFlat X) := by
          simpa [LinearMap.comp_apply] using hmetric
    _ = gradeMinusProj (E := E) Y := by rw [hXY]

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

section SolderingFixedPoints

/-- Equality of endomorphisms can be checked after transport through the native
    phase-space soldering equivalence.  This is the reusable operator form of
    soldering: it transports relations, not only individual vectors. -/
@[rep_depth krein] theorem soldering_operator_eq_iff
    (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (A B : Module.End ℝ (PhaseSpaceCarrier E))
    (C D : Module.End ℝ (DoubledSpace E))
    (hA : (toDoubledCopyRho (E := E) ρ).comp A = C.comp
      (toDoubledCopyRho (E := E) ρ))
    (hB : (toDoubledCopyRho (E := E) ρ).comp B = D.comp
      (toDoubledCopyRho (E := E) ρ)) :
    A = B ↔ C = D := by
  constructor
  · intro h
    apply LinearMap.ext
    intro Y
    let X : PhaseSpaceCarrier E := fromDoubledCopyRho (E := E) ρ Y
    have hA' := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X) hA
    have hB' := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X) hB
    calc
      C Y = C (toDoubledCopyRho (E := E) ρ X) := by
        rw [toDoubledCopyRho_fromDoubledCopyRho]
      _ = toDoubledCopyRho (E := E) ρ (A X) := by
        simpa [LinearMap.comp_apply] using hA'.symm
      _ = toDoubledCopyRho (E := E) ρ (B X) := by rw [h]
      _ = D (toDoubledCopyRho (E := E) ρ X) := by
        simpa [LinearMap.comp_apply] using hB'
      _ = D Y := by
        rw [toDoubledCopyRho_fromDoubledCopyRho]
  · intro h
    apply LinearMap.ext
    intro X
    have hA' := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X) hA
    have hB' := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X) hB
    have hCD := congrArg
      (fun F : Module.End ℝ (DoubledSpace E) => F
        (toDoubledCopyRho (E := E) ρ X)) h
    have hCD' : C (toDoubledCopyRho (E := E) ρ X) =
        D (toDoubledCopyRho (E := E) ρ X) := by
      simpa [Module.End.mul_apply] using hCD
    have hA'' : toDoubledCopyRho (E := E) ρ (A X) =
        C (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hA'
    have hB'' : toDoubledCopyRho (E := E) ρ (B X) =
        D (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hB'
    have htransport : toDoubledCopyRho (E := E) ρ (A X) =
        toDoubledCopyRho (E := E) ρ (B X) := hA''.trans (hCD'.trans hB''.symm)
    exact (doubledCopyRhoEquiv (E := E) ρ).injective htransport

/--
The generalized-metric `+1` projector has exactly the same fixed points after
transport through the native phase-space soldering map.  This is the converse
direction to the projector intertwining equation: no fixed-point information
is lost because `toDoubledCopyRho` is a linear equivalence.
-/
@[rep_depth krein] theorem plusProjector_fixed_iff_soldered
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (X : PhaseSpaceCarrier E) :
    G.plusProjector X = X ↔
      realizedPlusProjector (G := G) ρ
        (toDoubledCopyRho (E := E) ρ X) =
        toDoubledCopyRho (E := E) ρ X := by
  constructor
  · intro hX
    have htransport := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    have htransport' :
        toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
          realizedPlusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using htransport
    rw [hX] at htransport'
    exact htransport'.symm
  · intro hX
    have htransport := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    have htransport' :
        toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
          realizedPlusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using htransport
    have hsame :
        toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
          toDoubledCopyRho (E := E) ρ X := htransport'.trans hX
    have hback := congrArg
      (fun Y : DoubledSpace E => fromDoubledCopyRho (E := E) ρ Y) hsame
    simpa using hback

/- The `-1` projector obeys the same lossless soldering transport. -/
@[rep_depth krein] theorem minusProjector_fixed_iff_soldered
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (X : PhaseSpaceCarrier E) :
    G.minusProjector X = X ↔
      realizedMinusProjector (G := G) ρ
        (toDoubledCopyRho (E := E) ρ X) =
        toDoubledCopyRho (E := E) ρ X := by
  constructor
  · intro hX
    have htransport := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
    have htransport' :
        toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
          realizedMinusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using htransport
    rw [hX] at htransport'
    exact htransport'.symm
  · intro hX
    have htransport := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
    have htransport' :
        toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
          realizedMinusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using htransport
    have hsame :
        toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
          toDoubledCopyRho (E := E) ρ X := htransport'.trans hX
    have hback := congrArg
      (fun Y : DoubledSpace E => fromDoubledCopyRho (E := E) ρ Y) hsame
    simpa using hback

end SolderingFixedPoints

section SolderedProjectorAlgebra

/-! The native soldering equivalence transports the complete projector algebra.
    These are operator equalities on the doubled carrier, not merely pointwise
    fixed-point readouts. -/

@[rep_depth krein] theorem realizedPlusProjector_idempotent
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedPlusProjector (G := G) ρ * realizedPlusProjector (G := G) ρ =
      realizedPlusProjector (G := G) ρ := by
  apply LinearMap.ext
  intro Y
  let X : PhaseSpaceCarrier E := fromDoubledCopyRho (E := E) ρ Y
  have h₁ := congrArg
    (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
    (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
  have h₂ := congrArg
    (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F (G.plusProjector X))
    (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
  have h₁' : toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
      realizedPlusProjector (G := G) ρ Y := by
    simpa [X, LinearMap.comp_apply] using h₁
  have h₂' : toDoubledCopyRho (E := E) ρ (G.plusProjector (G.plusProjector X)) =
      realizedPlusProjector (G := G) ρ
        (toDoubledCopyRho (E := E) ρ (G.plusProjector X)) := by
    simpa [LinearMap.comp_apply] using h₂
  have hId : G.plusProjector (G.plusProjector X) = G.plusProjector X := by
    have h := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] PhaseSpaceCarrier E => F X)
      (GeneralizedMetricDatum.plusProjector_idempotent G)
    simpa [Module.End.mul_apply] using h
  calc
    (realizedPlusProjector (G := G) ρ * realizedPlusProjector (G := G) ρ) Y =
        realizedPlusProjector (G := G) ρ
          (realizedPlusProjector (G := G) ρ Y) := rfl
    _ = realizedPlusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ (G.plusProjector X)) := by rw [h₁']
    _ = toDoubledCopyRho (E := E) ρ
          (G.plusProjector (G.plusProjector X)) := by rw [h₂']
    _ = toDoubledCopyRho (E := E) ρ (G.plusProjector X) := by
      rw [hId]
    _ = realizedPlusProjector (G := G) ρ Y := h₁'

@[rep_depth krein] theorem realizedMinusProjector_idempotent
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedMinusProjector (G := G) ρ * realizedMinusProjector (G := G) ρ =
      realizedMinusProjector (G := G) ρ := by
  apply LinearMap.ext
  intro Y
  let X : PhaseSpaceCarrier E := fromDoubledCopyRho (E := E) ρ Y
  have h₁ := congrArg
    (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
    (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
  have h₂ := congrArg
    (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F (G.minusProjector X))
    (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
  have h₁' : toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
      realizedMinusProjector (G := G) ρ Y := by
    simpa [X, LinearMap.comp_apply] using h₁
  have h₂' : toDoubledCopyRho (E := E) ρ (G.minusProjector (G.minusProjector X)) =
      realizedMinusProjector (G := G) ρ
        (toDoubledCopyRho (E := E) ρ (G.minusProjector X)) := by
    simpa [LinearMap.comp_apply] using h₂
  have hId : G.minusProjector (G.minusProjector X) = G.minusProjector X := by
    have h := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] PhaseSpaceCarrier E => F X)
      (GeneralizedMetricDatum.minusProjector_idempotent G)
    simpa [Module.End.mul_apply] using h
  calc
    (realizedMinusProjector (G := G) ρ * realizedMinusProjector (G := G) ρ) Y =
        realizedMinusProjector (G := G) ρ
          (realizedMinusProjector (G := G) ρ Y) := rfl
    _ = realizedMinusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ (G.minusProjector X)) := by rw [h₁']
    _ = toDoubledCopyRho (E := E) ρ
          (G.minusProjector (G.minusProjector X)) := by rw [h₂']
    _ = toDoubledCopyRho (E := E) ρ (G.minusProjector X) := by
      rw [hId]
    _ = realizedMinusProjector (G := G) ρ Y := h₁'

end SolderedProjectorAlgebra

section SolderedProjectorRelations

@[rep_depth krein] theorem realizedPlusProjector_add_realizedMinusProjector
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedPlusProjector (G := G) ρ + realizedMinusProjector (G := G) ρ =
      (1 : Module.End ℝ (DoubledSpace E)) := by
  refine (soldering_operator_eq_iff (ρ := ρ)
    (A := G.plusProjector + G.minusProjector)
    (B := (1 : Module.End ℝ (PhaseSpaceCarrier E)))
    (C := realizedPlusProjector (G := G) ρ + realizedMinusProjector (G := G) ρ)
    (D := (1 : Module.End ℝ (DoubledSpace E))) ?_ ?_).mp ?_
  · apply LinearMap.ext
    intro X
    have hp := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    have hm := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
    have hp' : toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
        realizedPlusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hp
    have hm' : toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
        realizedMinusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hm
    change toDoubledCopyRho (E := E) ρ
        (G.plusProjector X + G.minusProjector X) =
      realizedPlusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X) +
        realizedMinusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X)
    rw [map_add, hp', hm']
  · apply LinearMap.ext
    intro X
    simp [LinearMap.comp_apply]
  exact GeneralizedMetricDatum.plusProjector_add_minusProjector G

@[rep_depth krein] theorem realizedPlusProjector_mul_realizedMinusProjector
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedPlusProjector (G := G) ρ * realizedMinusProjector (G := G) ρ =
      (0 : Module.End ℝ (DoubledSpace E)) := by
  refine (soldering_operator_eq_iff (ρ := ρ)
    (A := G.plusProjector * G.minusProjector)
    (B := (0 : Module.End ℝ (PhaseSpaceCarrier E)))
    (C := realizedPlusProjector (G := G) ρ * realizedMinusProjector (G := G) ρ)
    (D := (0 : Module.End ℝ (DoubledSpace E))) ?_ ?_).mp ?_
  · apply LinearMap.ext
    intro X
    have hm := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
    have hp := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F (G.minusProjector X))
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    have hprod := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    change toDoubledCopyRho (E := E) ρ
        (G.plusProjector (G.minusProjector X)) =
      realizedPlusProjector (G := G) ρ
        (realizedMinusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ X))
    have hm' : toDoubledCopyRho (E := E) ρ (G.minusProjector X) =
        realizedMinusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hm
    have hp' : toDoubledCopyRho (E := E) ρ
        (G.plusProjector (G.minusProjector X)) =
        realizedPlusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ (G.minusProjector X)) := by
      simpa [LinearMap.comp_apply] using hp
    calc
      toDoubledCopyRho (E := E) ρ
          (G.plusProjector (G.minusProjector X)) =
          realizedPlusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ (G.minusProjector X)) := hp'
      _ = realizedPlusProjector (G := G) ρ
          (realizedMinusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X)) := by
            rw [hm']
  · apply LinearMap.ext
    intro X
    simp
  exact InfoGeometry.Cartan.Pplus_comp_Pminus G.polarization
    G.polarization_is_cartan

@[rep_depth krein] theorem realizedMinusProjector_mul_realizedPlusProjector
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedMinusProjector (G := G) ρ * realizedPlusProjector (G := G) ρ =
      (0 : Module.End ℝ (DoubledSpace E)) := by
  refine (soldering_operator_eq_iff (ρ := ρ)
    (A := G.minusProjector * G.plusProjector)
    (B := (0 : Module.End ℝ (PhaseSpaceCarrier E)))
    (C := realizedMinusProjector (G := G) ρ * realizedPlusProjector (G := G) ρ)
    (D := (0 : Module.End ℝ (DoubledSpace E))) ?_ ?_).mp ?_
  · apply LinearMap.ext
    intro X
    have hp := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_plusProjector_eq_realized (G := G) ρ)
    have hm := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F (G.plusProjector X))
      (toDoubledCopyRho_comp_minusProjector_eq_realized (G := G) ρ)
    have hp' : toDoubledCopyRho (E := E) ρ (G.plusProjector X) =
        realizedPlusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using hp
    have hm' : toDoubledCopyRho (E := E) ρ
        (G.minusProjector (G.plusProjector X)) =
        realizedMinusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ (G.plusProjector X)) := by
      simpa [LinearMap.comp_apply] using hm
    change toDoubledCopyRho (E := E) ρ
        (G.minusProjector (G.plusProjector X)) =
      realizedMinusProjector (G := G) ρ
        (realizedPlusProjector (G := G) ρ
          (toDoubledCopyRho (E := E) ρ X))
    calc
      toDoubledCopyRho (E := E) ρ
          (G.minusProjector (G.plusProjector X)) =
          realizedMinusProjector (G := G) ρ
            (toDoubledCopyRho (E := E) ρ (G.plusProjector X)) := hm'
      _ = realizedMinusProjector (G := G) ρ
          (realizedPlusProjector (G := G) ρ (toDoubledCopyRho (E := E) ρ X)) := by
            rw [hp']
  · apply LinearMap.ext
    intro X
    simp
  exact InfoGeometry.Cartan.Pminus_comp_Pplus G.polarization
    G.polarization_is_cartan

end SolderedProjectorRelations

section SolderedPolarization

/-! The same soldering map transports the generalized metric readout, not only
the polarization operator.  The form is defined by pullback along the native
linear equivalence; its evaluation theorem is the reusable soldering law. -/

@[rep_depth krein]
noncomputable def realizedGeneralizedMetricForm
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    LinearMap.BilinForm ℝ (DoubledSpace E) :=
  LinearMap.BilinForm.comp G.generalizedMetricForm
    (fromDoubledCopyRho (E := E) ρ)
    (fromDoubledCopyRho (E := E) ρ)

@[rep_depth krein, simp] theorem realizedGeneralizedMetricForm_apply
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (X Y : PhaseSpaceCarrier E) :
    realizedGeneralizedMetricForm (G := G) ρ
        (toDoubledCopyRho (E := E) ρ X)
        (toDoubledCopyRho (E := E) ρ Y) =
      G.generalizedMetricForm X Y := by
  simp [realizedGeneralizedMetricForm, LinearMap.BilinForm.comp_apply]

@[rep_depth krein] theorem realizedGeneralizedMetricForm_symm
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (X Y : DoubledSpace E) :
    realizedGeneralizedMetricForm (G := G) ρ X Y =
      realizedGeneralizedMetricForm (G := G) ρ Y X := by
  rw [realizedGeneralizedMetricForm, LinearMap.BilinForm.comp_apply,
    LinearMap.BilinForm.comp_apply, G.generalizedMetricForm_symm]

@[rep_depth krein]
noncomputable def realizedGeneralizedMetricQuadraticForm
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    QuadraticForm ℝ (DoubledSpace E) :=
  G.generalizedMetricQuadraticForm.comp
    (fromDoubledCopyRho (E := E) ρ)

@[rep_depth krein, simp] theorem realizedGeneralizedMetricQuadraticForm_apply
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E)
    (X : PhaseSpaceCarrier E) :
    realizedGeneralizedMetricQuadraticForm (G := G) ρ
        (toDoubledCopyRho (E := E) ρ X) =
      G.generalizedMetricQuadraticForm X := by
  simp [realizedGeneralizedMetricQuadraticForm]

@[rep_depth krein] theorem realizedGeneralizedMetricQuadraticForm_eq_diagonal
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedGeneralizedMetricQuadraticForm (G := G) ρ =
      (realizedGeneralizedMetricForm (G := G) ρ).toQuadraticMap := by
  ext X
  change G.generalizedMetricQuadraticForm
      (fromDoubledCopyRho (E := E) ρ X) =
    G.generalizedMetricForm
      (fromDoubledCopyRho (E := E) ρ X)
      (fromDoubledCopyRho (E := E) ρ X)
  exact G.generalizedMetricQuadraticForm_apply _

/-- The native soldering equivalence preserves the generalized-metric
    polarization involution. -/
@[rep_depth krein] theorem realizedPolarization_sq
    (G : GeneralizedMetricDatum E) (ρ : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    realizedPolarization (G := G) ρ * realizedPolarization (G := G) ρ =
      (1 : Module.End ℝ (DoubledSpace E)) := by
  refine (soldering_operator_eq_iff (ρ := ρ)
    (A := G.polarization * G.polarization)
    (B := (1 : Module.End ℝ (PhaseSpaceCarrier E)))
    (C := realizedPolarization (G := G) ρ * realizedPolarization (G := G) ρ)
    (D := (1 : Module.End ℝ (DoubledSpace E))) ?_ ?_).mp ?_
  · apply LinearMap.ext
    intro X
    have h₁ := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E =>
        F (G.polarization X))
      (toDoubledCopyRho_comp_polarization_eq_realized (G := G) ρ)
    have h₂ := congrArg
      (fun F : PhaseSpaceCarrier E →ₗ[ℝ] DoubledSpace E => F X)
      (toDoubledCopyRho_comp_polarization_eq_realized (G := G) ρ)
    have h₁' : toDoubledCopyRho (E := E) ρ
        (G.polarization (G.polarization X)) =
        realizedPolarization (G := G) ρ
          (toDoubledCopyRho (E := E) ρ (G.polarization X)) := by
      simpa [LinearMap.comp_apply] using h₁
    have h₂' : toDoubledCopyRho (E := E) ρ (G.polarization X) =
        realizedPolarization (G := G) ρ
          (toDoubledCopyRho (E := E) ρ X) := by
      simpa [LinearMap.comp_apply] using h₂
    change toDoubledCopyRho (E := E) ρ
        (G.polarization (G.polarization X)) =
      realizedPolarization (G := G) ρ
        (realizedPolarization (G := G) ρ
          (toDoubledCopyRho (E := E) ρ X))
    calc
      toDoubledCopyRho (E := E) ρ
          (G.polarization (G.polarization X)) =
          realizedPolarization (G := G) ρ
            (toDoubledCopyRho (E := E) ρ (G.polarization X)) := h₁'
      _ = realizedPolarization (G := G) ρ
          (realizedPolarization (G := G) ρ
            (toDoubledCopyRho (E := E) ρ X)) := by rw [h₂']
  · apply LinearMap.ext
    intro X
    simp [LinearMap.comp_apply]
  exact GeneralizedMetricDatum.polarization_sq G

end SolderedPolarization

end Core

end InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
