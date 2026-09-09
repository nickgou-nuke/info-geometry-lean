import InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Meta.Architecture

/-!
# Generalized soldering for the neutral phase-space owner

The existing generalized-metric owner supplies a metric duality and a skew
`B`-field on `E`.  This file supplies the missing finite soldering edge:

`E × E  ≃ₗ  E × E*`,

where the second frame leg is raised by the metric and the first leg is
shifted by the `B`-field.  The inverse and the pullback of the neutral
pairing are proved directly.  No new generalized-metric or doubled-space
carrier is introduced.
-/

namespace InfoGeometry.Canonical.GeneralizedSolderingBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric
open InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric.GeneralizedMetricDatum

section Core

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The generalized frame soldering map `(x,y) ↦ (x, g♭ y + B x)`. -/
@[rep_depth krein]
noncomputable def generalizedSoldering
    (G : GeneralizedMetricDatum E) :
    (E × E) ≃ₗ[ℝ] PhaseSpaceCarrier E :=
  LinearEquiv.ofLinear
    { toFun := fun X => (X.1, G.metric.gFlat X.2 + G.bField.twist X.1)
      map_add' := by
        intro X Y
        refine Prod.ext ?_ ?_
        · simp
        · simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro r X
        refine Prod.ext ?_ ?_
        · simp
        · simp [smul_add] }
    { toFun := fun X =>
        (X.1, G.metric.gFlat.symm (X.2 - G.bField.twist X.1))
      map_add' := by
        intro X Y
        refine Prod.ext ?_ ?_
        · simp
        · simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro r X
        refine Prod.ext ?_ ?_
        · simp
        · simp [sub_eq_add_neg, smul_add] }
    (by
      apply LinearMap.ext
      intro X
      rcases X with ⟨x, y⟩
      apply Prod.ext
      · rfl
      · simp)
    (by
      apply LinearMap.ext
      intro X
      rcases X with ⟨x, φ⟩
      apply Prod.ext
      · rfl
      · simp)

@[rep_depth krein, simp] theorem generalizedSoldering_apply
    (G : GeneralizedMetricDatum E) (x y : E) :
    generalizedSoldering G (x, y) =
      (x, G.metric.gFlat y + G.bField.twist x) := rfl

@[rep_depth krein, simp] theorem generalizedSoldering_symm_apply
    (G : GeneralizedMetricDatum E) (x : E) (φ : Module.Dual ℝ E) :
    (generalizedSoldering G).symm (x, φ) =
      (x, G.metric.gFlat.symm (φ - G.bField.twist x)) := rfl

@[rep_depth krein, simp] theorem generalizedSoldering_eq_bTransform_metricLift
    (G : GeneralizedMetricDatum E) (x y : E) :
    generalizedSoldering G (x, y) =
      G.bTransform (x, G.metric.gFlat y) := by
  simp [generalizedSoldering_apply, bTransform_apply, add_comm]

/-- The generalized-metric polarization is the coordinate swap in the
    soldered frame. -/
@[rep_depth krein, simp] theorem generalizedSoldering_polarization_swap
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.polarization (generalizedSoldering G (x, y)) =
      generalizedSoldering G (y, x) := by
  simp [generalizedSoldering_apply, polarization_apply, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- The `+` generalized-metric projector is the symmetric coordinate part in
    the soldered frame. -/
@[rep_depth krein, simp] theorem generalizedSoldering_plusProjector
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.plusProjector (generalizedSoldering G (x, y)) =
      (⅟ (2 : ℝ)) •
        (generalizedSoldering G (x, y) + generalizedSoldering G (y, x)) := by
  rw [plusProjector, InfoGeometry.Cartan.Pplus_apply,
    generalizedSoldering_polarization_swap]

/-- The `-` generalized-metric projector is the antisymmetric coordinate part
    in the soldered frame. -/
@[rep_depth krein, simp] theorem generalizedSoldering_minusProjector
    (G : GeneralizedMetricDatum E) (x y : E) :
    G.minusProjector (generalizedSoldering G (x, y)) =
      (⅟ (2 : ℝ)) •
        (generalizedSoldering G (x, y) - generalizedSoldering G (y, x)) := by
  rw [minusProjector, InfoGeometry.Cartan.Pminus_apply,
    generalizedSoldering_polarization_swap]

@[rep_depth krein, simp] theorem generalizedSoldering_apply_symm_apply
    (G : GeneralizedMetricDatum E) (X : PhaseSpaceCarrier E) :
    generalizedSoldering G ((generalizedSoldering G).symm X) = X := by
  exact (generalizedSoldering G).apply_symm_apply X

@[rep_depth krein, simp] theorem generalizedSoldering_symm_apply_apply
    (G : GeneralizedMetricDatum E) (X : E × E) :
    (generalizedSoldering G).symm (generalizedSoldering G X) = X := by
  exact (generalizedSoldering G).symm_apply_apply X

@[rep_depth krein] theorem generalizedSoldering_neutralPairing
    (G : GeneralizedMetricDatum E) (X Y : E × E) :
    canonicalNeutralBilin (E := E)
        (generalizedSoldering G X) (generalizedSoldering G Y) =
      G.metric.gFlat X.2 Y.1 + G.metric.gFlat Y.2 X.1 := by
  rcases X with ⟨x, y⟩
  rcases Y with ⟨x', y'⟩
  rw [generalizedSoldering_apply, generalizedSoldering_apply,
    canonicalNeutralBilin_apply]
  have hB : G.bField.twist x x' + G.bField.twist x' x = 0 := by
    rw [G.bField.skew x x']
    abel
  have hmetric₁ : G.metric.gFlat y x' = G.metric.gFlat x' y :=
    G.metric.symmetric y x'
  have hmetric₂ : G.metric.gFlat y' x = G.metric.gFlat x y' :=
    G.metric.symmetric y' x
  simp only [LinearMap.add_apply]
  rw [hmetric₁, hmetric₂]
  calc
    G.metric.gFlat x' y + (G.bField.twist x) x' +
          (G.metric.gFlat x y' + (G.bField.twist x') x) =
        G.metric.gFlat x' y + G.metric.gFlat x y' +
          ((G.bField.twist x) x' + (G.bField.twist x') x) := by ring
    _ = G.metric.gFlat x' y + G.metric.gFlat x y' := by rw [hB, add_zero]

@[rep_depth krein] theorem generalizedSoldering_neutralQuadratic
    (G : GeneralizedMetricDatum E) (X : E × E) :
    canonicalNeutralForm (E := E) (generalizedSoldering G X) =
      2 * G.metric.gFlat X.2 X.1 := by
  rw [canonicalNeutralForm_apply]
  rcases X with ⟨x, y⟩
  rw [generalizedSoldering_apply]
  simp only [LinearMap.add_apply]
  have hB : G.bField.twist x x = 0 := by
    have h := G.bField.skew x x
    linarith
  rw [hB, add_zero]

/-- The generalized metric in soldered frame coordinates.  This is the
    pullback formula for the existing owner-side bilinear form; it introduces
    no second metric or parallel frame carrier. -/
@[rep_depth krein] theorem generalizedSoldering_generalizedMetricForm
    (G : GeneralizedMetricDatum E) (X Y : E × E) :
    G.generalizedMetricForm (generalizedSoldering G X)
        (generalizedSoldering G Y) =
      G.metric.gFlat X.2 Y.2 + G.metric.gFlat Y.1 X.1 := by
  rcases X with ⟨x, y⟩
  rcases Y with ⟨x', y'⟩
  rw [generalizedMetricForm_apply, generalizedSoldering_polarization_swap]
  simpa using generalizedSoldering_neutralPairing G (x, y) (y', x')

@[rep_depth krein] theorem generalizedSoldering_generalizedMetricQuadraticForm
    (G : GeneralizedMetricDatum E) (X : E × E) :
    G.generalizedMetricQuadraticForm (generalizedSoldering G X) =
      G.metric.gFlat X.2 X.2 + G.metric.gFlat X.1 X.1 := by
  rw [generalizedMetricQuadraticForm_apply]
  simpa using generalizedSoldering_generalizedMetricForm G X X

end Core

end InfoGeometry.Canonical.GeneralizedSolderingBridge
